import OS4.Words.Interpreter
import OS4.Words.Blocks
import OS4.Words.Output
import OS4.Steps
import OS4.Memory

/-!
# Wordlist search, and what the interpreter's words write

A search order of one wordlist finds only that wordlist's words (`find_name_one`),
and the words INTERPRET calls write nothing, or only `>in` or `base` (their
`Frame`s). `OS4.Isolation` builds on both.
-/

namespace OS4.Isolation
open OS4

/-! ## Wordlists in memory -/

/-- The headers from nt back along their links, ending at 0: a wordlist's
words, newest first, as `search-list` walks them. -/
inductive Chain (m : Mem) : Cell → List Cell → Prop
  | nil : Chain m 0 []
  | cons {h : Cell} {hs : List Cell} : h ≠ 0 → Chain m (rd m h 8) hs → Chain m h (h :: hs)

/-- Whatever `search_sub` finds walking a chain is on it, or 0. -/
theorem walk_on (m : Mem) (a u x : Cell) :
    ∀ (n : Nat) (nt : Cell) (hs : List Cell), Chain m nt hs → Prim.walk m a u n nt = some x →
      x = 0 ∨ x ∈ hs := by
  intro n
  induction n with
  | zero => intro nt hs _ h; simp [Prim.walk] at h
  | succ n ih =>
    intro nt hs hc h
    cases hc with
    | nil => simp [Prim.walk] at h; exact Or.inl h.symm
    | cons h0 hc' =>
      simp only [Prim.walk, if_neg h0] at h
      split at h
      · simp at h; subst h; exact Or.inr (by simp)
      · rcases ih _ _ hc' h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem _ h')

/-- A walk along a chain ends within its length. -/
theorem walk_ends (m : Mem) (a u : Cell) :
    ∀ (nt : Cell) (hs : List Cell), Chain m nt hs → (Prim.walk m a u (hs.length + 1) nt).isSome := by
  intro nt hs hc
  induction hc with
  | nil => simp [Prim.walk]
  | cons h0 _ ih =>
    simp only [Prim.walk, if_neg h0, List.length_cons]
    split
    · rfl
    · exact ih

/-- SEARCH-LIST on a chain returns one of its headers, or 0. -/
theorem searchList_chain (nt u a : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (hs : List Cell) (hc : Chain m nt hs) :
    ∃ x, (x = 0 ∨ x ∈ hs) ∧
      Prim.searchList ⟨nt :: u :: a :: s, r, m, p, e⟩ = .ok ⟨x :: s, r, m, p, e⟩ := by
  have ex : ∃ n, (Prim.walk m a u n nt).isSome := ⟨_, walk_ends m a u nt hs hc⟩
  refine ⟨_, ?_, by unfold Prim.searchList; dsimp only; rw [dif_pos ex]⟩
  exact walk_on m a u _ _ nt hs hc (Option.some_get _).symm

/-! ## FIND-NAME with one wordlist -/

/-- The user-area cells that hold the search order (`#order`, `context`). -/
abbrev uOrder : Cell := 352
abbrev uContext : Cell := 360

/-- The cell `current` keeps the compilation wordlist in. -/
noncomputable abbrev currentA : Cell := wordAddr "current" + 8

set_option maxHeartbeats 4000000 in
/-- With a search order of one wordlist wid (not the compilation wordlist,
whose newest word is `latest`), FIND-NAME returns one of wid's headers, or 0,
and changes nothing else. -/
theorem find_name_one (u a wid : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (hs : List Cell) (h1 : rd m (uOrder + p) 8 = 1) (h2 : rd m (uContext + p) 8 = wid)
    (hcur : wid ≠ rd m currentA 8) (hc : Chain m (rd m wid 8) hs) :
    ∃ x, (x = 0 ∨ x ∈ hs) ∧ Words.«find-name» ⟨u :: a :: s, r, m, p, e⟩ = .ok ⟨x :: s, r, m, p, e⟩ := by
  obtain ⟨x, hx, hsl⟩ := searchList_chain (rd m wid 8) u a (u :: a :: s) (0#64 :: 1#64 :: r) m p e hs hc
  refine ⟨x, hx, ?_⟩
  apply loopThread_eq _ _ 40 _ _ (by simp [outOfFuel])
  simp only [uOrder, uContext, currentA] at h1 h2 hcur
  simp at h1 h2 hcur
  by_cases hx0 : x = 0#64
  · subst hx0
    simp [forth, h1, h2, hcur, hsl]
  · simp [forth, h1, h2, hcur, hsl, hx0]

/-! ## Frames of the words INTERPRET calls -/

section
variable (W : Cell → Cell → Prop)
open Prim

theorem true_frame : Frame W Words.«true» := pushConst_frame _ W
theorem false_frame : Frame W Words.«false» := pushConst_frame _ W
theorem bl_frame : Frame W Words.«bl» := pushConst_frame _ W
theorem rot_frame : Frame W Words.«rot» :=
  thread_frame (by simp only [Words.«rot».code]; frames [tor_frame, swap_frame, rfrom_frame])
theorem mrot_frame : Frame W Words.«-rot» :=
  thread_frame (by simp only [Words.«-rot».code]; frames [rot_frame])
theorem tuck_frame : Frame W Words.«tuck» :=
  thread_frame (by simp only [Words.«tuck».code]; frames [swap_frame, over_frame])
theorem nip_frame : Frame W Words.«nip» :=
  thread_frame (by simp only [Words.«nip».code]; frames [swap_frame, drop_frame])
theorem twodup_frame : Frame W Words.«2dup» :=
  thread_frame (by simp only [Words.«2dup».code]; frames [over_frame])
theorem twodrop_frame : Frame W Words.«2drop» :=
  thread_frame (by simp only [Words.«2drop».code]; frames [drop_frame])
theorem qdup_frame : Frame W Words.«?dup» :=
  thread_frame (by simp only [Words.«?dup».code]; frames [dup_frame])
theorem oneplus_frame : Frame W Words.«1+» :=
  thread_frame (by simp only [Words.«1+».code]; frames [plus_frame])
theorem negate_frame : Frame W Words.«negate» :=
  thread_frame (by simp only [Words.«negate».code]; frames [swap_frame, minus_frame])
theorem cellplus_frame : Frame W Words.«cell+» :=
  thread_frame (by simp only [Words.«cell+».code]; frames [plus_frame])
theorem zne_frame : Frame W Words.«0<>» :=
  thread_frame (by simp only [Words.«0<>».code]; frames [zequal_frame])
theorem ugreater_frame : Frame W Words.«u>» :=
  thread_frame (by simp only [Words.«u>».code]; frames [swap_frame, uless_frame])
theorem greater_frame : Frame W Words.«>» :=
  thread_frame (by simp only [Words.«>».code]; frames [swap_frame, less_frame])
theorem aligned_frame : Frame W Words.«aligned» :=
  thread_frame (by simp only [Words.«aligned».code]; frames [plus_frame, and_frame])
theorem name_string_frame : Frame W Words.«name>string» :=
  thread_frame (by simp only [Words.«name>string».code]
                   frames [cellplus_frame, dup_frame, oneplus_frame, swap_frame, cfetch_frame,
                     pushConst_frame _, and_frame])
theorem name_xt_frame : Frame W Words.«name>xt» :=
  thread_frame (by simp only [Words.«name>xt».code]; frames [name_string_frame, plus_frame, aligned_frame])
theorem within_frame : Frame W Words.«within» :=
  thread_frame (by simp only [Words.«within».code]
                   frames [over_frame, minus_frame, tor_frame, rfrom_frame, uless_frame])
theorem slash_string_frame : Frame W Words.«/string» :=
  thread_frame (by simp only [Words.«/string».code]
                   frames [tuck_frame, minus_frame, tor_frame, plus_frame, rfrom_frame])
theorem lower_frame : Frame W Words.«lower» :=
  thread_frame (by simp only [Words.«lower».code]; frames [dup_frame, oneplus_frame, within_frame, plus_frame])
theorem compile_only_frame : Frame W Words.«compile-only?» :=
  thread_frame (by simp only [Words.«compile-only?».code]
                   frames [cellplus_frame, cfetch_frame, pushConst_frame _, and_frame, zne_frame])
theorem immediate_frame : Frame W Words.«immediate?» :=
  thread_frame (by simp only [Words.«immediate?».code]
                   frames [cellplus_frame, cfetch_frame, pushConst_frame _, and_frame, zne_frame])
theorem qstack_frame : Frame W Words.«?stack» :=
  thread_frame (by simp only [Words.«?stack».code]
                   frames [depth_frame, zless_frame, throwM_frame, kconst_frame _, userAt_frame _,
                     fetch_frame, ugreater_frame])
theorem digit_frame : Frame W Words.«digit?» :=
  thread_frame (by simp only [Words.«digit?».code]
                   frames [lower_frame, dup_frame, oneplus_frame, within_frame, minus_frame, drop_frame,
                     false_frame, userAt_frame _, fetch_frame, less_frame, true_frame])
theorem prefix_base_frame : Frame W Words.«prefix-base» :=
  thread_frame (by simp only [Words.«prefix-base».code]; frames [dup_frame, equal_frame, drop_frame])
theorem number_digits_frame : Frame W Words.«(number)» :=
  loopThread_frame (by simp only [Words.«(number)».code]
                       frames [dup_frame, zequal_frame, twodrop_frame, false_frame, mrot_frame,
                         over_frame, cfetch_frame, digit_frame, drop_frame, tor_frame, rot_frame,
                         userAt_frame _, fetch_frame, star_frame, rfrom_frame, plus_frame,
                         slash_string_frame, true_frame])
theorem source_frame : Frame W Words.«source» :=
  thread_frame (by simp only [Words.«source».code]; frames [userAt_frame _, fetch_frame])
theorem end_frame : Frame W Words.«end?» :=
  thread_frame (by simp only [Words.«end?».code]
                   frames [userAt_frame _, fetch_frame, less_frame, zequal_frame])
theorem char_fetch_frame : Frame W Words.«char@» :=
  thread_frame (by simp only [Words.«char@».code]
                   frames [source_frame, drop_frame, userAt_frame _, fetch_frame, plus_frame, cfetch_frame])
theorem oneminus_frame : Frame W Words.«1-» :=
  thread_frame (by simp only [Words.«1-».code]; frames [minus_frame])
theorem twostar_frame : Frame W Words.«2*» :=
  thread_frame (by simp only [Words.«2*».code]; frames [lshift_frame])
theorem slash_frame : Frame W Words.«/» :=
  thread_frame (by simp only [Words.«/».code]; frames [slashmod_frame, nip_frame])
theorem mod_frame : Frame W Words.«mod» :=
  thread_frame (by simp only [Words.«mod».code]; frames [slashmod_frame, drop_frame])
theorem ne_frame : Frame W Words.«<>» :=
  thread_frame (by simp only [Words.«<>».code]; frames [equal_frame, zequal_frame])
theorem abs_frame : Frame W Words.«abs» :=
  thread_frame (by simp only [Words.«abs».code]; frames [dup_frame, zless_frame, negate_frame])
theorem min_frame : Frame W Words.«min» :=
  thread_frame (by simp only [Words.«min».code]; frames [twodup_frame, greater_frame, swap_frame, drop_frame])
theorem max_frame : Frame W Words.«max» :=
  thread_frame (by simp only [Words.«max».code]; frames [twodup_frame, less_frame, swap_frame, drop_frame])
end

/-- A cell written at a leaves every byte 8 or more past it alone. -/
theorem wr_far (m : Mem) (a v x : Cell) (hx : 8 ≤ (x - a).toNat) : wr m a 8 v x = m x := by
  apply wr_apply_other x 8 m a v
  intro j hj hxa
  subst hxa
  have : (BitVec.ofNat 64 j).toNat = j := by simp; omega
  simp [this] at hx
  omega

theorem plus_store_at : StoreAt Words.«+!» := by
  intro s s' a t hds h
  rcases s with ⟨ds, rs, m, u, e⟩
  simp only at hds
  subst hds
  cases t with
  | nil => simp [forth, S.fail] at h
  | cons v t =>
    simp [forth] at h
    subst h
    exact ⟨rfl, fun x hx => wr_far m a _ x hx⟩

/-- `>in`'s cell, the one PARSE-NAME writes. -/
abbrev toinCell (p a : Cell) : Prop := (a - (p + 16)).toNat < 8
/-- `base`'s cell, which NUMBER? sets and restores for a prefix such as `$`. -/
abbrev baseCell (p a : Cell) : Prop := (a - (p + 0)).toNat < 8

theorem parse_name_frame : Frame toinCell Words.«parse-name#2» :=
  (thread_frame_at (P := [10, 26, 40]) (off := 16) (by decide) (fun s0 => by
    simp only [Words.«parse-name#2».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
    keeps [end_frame, Prim.zequal_frame, char_fetch_frame, bl_frame, greater_frame, source_frame,
      Prim.drop_frame, Prim.fetch_frame, Prim.plus_frame, Prim.over_frame, Prim.minus_frame] [plus_store_at])).2

theorem paren_frame : Frame toinCell Prim.paren := by
  intro s s' h
  rcases s with ⟨ds, rs, m, p, e⟩
  simp only [Prim.paren, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, fun a ha => wr_far m _ _ a (by simp only [toinCell] at ha; simp only [Prim.uToin]; omega)⟩

theorem backslash_frame : Frame toinCell Words.«\#2» :=
  (thread_frame_at (P := [13]) (off := 16) (by decide) (fun s0 => by
    simp only [Words.«\#2».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
    keeps [userAt_frame _, Prim.fetch_frame, Prim.plus_frame, Prim.and_frame] [store_at])).1

theorem hex_frame : Frame baseCell Words.«hex» :=
  (thread_frame_at (P := [2]) (off := 0) (by decide) (fun s0 => by
    simp only [Words.«hex».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
    keeps [] [store_at])).1

theorem decimal_frame : Frame baseCell Words.«decimal» :=
  (thread_frame_at (P := [2]) (off := 0) (by decide) (fun s0 => by
    simp only [Words.«decimal».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
    keeps [] [store_at])).1

theorem number_frame : Frame baseCell Words.«number?» :=
  (thread_frame_at (P := [47, 53]) (off := 0) (by decide) (fun s0 => by
    simp only [Words.«number?».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
    keeps [Prim.dup_frame, Prim.equal_frame, Prim.over_frame, Prim.cfetch_frame, Prim.drop_frame, oneplus_frame, true_frame,
      Prim.tor_frame, Prim.plus_frame, slash_string_frame, Prim.zequal_frame, twodrop_frame, Prim.rfrom_frame, false_frame,
      prefix_base_frame, qdup_frame, Prim.fetch_frame, number_digits_frame, negate_frame] [store_at])).1

end OS4.Isolation

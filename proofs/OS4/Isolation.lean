import OS4.Search
import OS4.Words.Sandbox

/-!
# Sandbox isolation (V2)

The brief's rule: a player-facing wordlist never reaches the full dictionary.
Here it is a theorem about INTERPRET as compiled. A task whose search order
is one wordlist (the sandbox) executes only that wordlist's words: replace
EXECUTE in INTERPRET by anything that agrees with it on those words' xts, and
INTERPRET's result does not change, whatever the line holds.

What it assumes, besides the model:

* the setting (`Box.Ok`): the search order is the sandbox alone, which is not
  the compilation wordlist; STATE is 0; the sandbox's headers form a chain
  that ends; and the dictionary bytes this rests on are not in the first 24
  bytes of the task's user area (where `base` and `>in` are);
* that the sandbox's own words keep this setting when they run (`hkeep`).
  That is the next theorem to prove, word by word, from their footprints.
-/

namespace OS4.Isolation
open OS4

/-! ## The setting -/

/-- The task's user area p, the sandbox wordlist wid, its headers hs (newest
first), and memory m0 when INTERPRET starts. -/
structure Box where
  p : Cell
  wid : Cell
  hs : List Cell
  m0 : Mem

namespace Box
variable (B : Box)

/-- The user-area bytes isolation rests on: STATE, `#order` and `context`. -/
def userSupp (a : Cell) : Prop := (a - (B.p + 8)).toNat < 8 ∨ (a - (B.p + 352)).toNat < 16
/-- The dictionary bytes it rests on: `current`, the wordlist's cell, and
each header's link and length byte. -/
def dictSupp (a : Cell) : Prop :=
  (a - currentA).toNat < 8 ∨ (a - B.wid).toNat < 8 ∨ ∃ h ∈ B.hs, (a - h).toNat < 9
def supp (a : Cell) : Prop := B.userSupp a ∨ B.dictSupp a

/-- Memory still holds those bytes as they were. -/
def Inv (m : Mem) : Prop := ∀ a, B.supp a → m a = B.m0 a

/-- The xt of the header at h (NAME>XT). -/
def xtOf (m : Mem) (h : Cell) : Cell := (h + 8 + 1 + (rd m (h + 8) 1 &&& 31) + 7) &&& 18446744073709551608

/-- The xts of the sandbox's words. -/
def Allowed (xt : Cell) : Prop := ∃ h ∈ B.hs, xt = xtOf B.m0 h

structure Ok : Prop where
  order : rd B.m0 (uOrder + B.p) 8 = 1
  context : rd B.m0 (uContext + B.p) 8 = B.wid
  state : rd B.m0 (B.p + 8) 8 = 0
  notCurrent : B.wid ≠ rd B.m0 currentA 8
  chain : Chain B.m0 (rd B.m0 B.wid 8) B.hs
  apart : ∀ a, B.dictSupp a → 24 ≤ (a - B.p).toNat

end Box

/-! ## What the invariant gives -/

theorem chain_congr {m m' : Mem} :
    ∀ {nt : Cell} {hs : List Cell}, Chain m nt hs → (∀ h ∈ hs, rd m' h 8 = rd m h 8) → Chain m' nt hs := by
  intro nt hs hc
  induction hc with
  | nil => intro _; exact Chain.nil
  | cons h0 _ ih =>
    intro hl
    refine Chain.cons h0 ?_
    rw [hl _ (List.mem_cons_self ..)]
    exact ih fun h hh => hl h (List.mem_cons_of_mem _ hh)

section
variable {B : Box} {m : Mem}

theorem Box.rd_eq (hI : B.Inv m) (x : Cell) (n : Nat) (hx : ∀ i, i < n → B.supp (x + BitVec.ofNat 64 i)) :
    rd m x n = rd B.m0 x n :=
  rd_congr m B.m0 n x fun i hi => hI _ (hx i hi)

theorem Box.facts (hB : B.Ok) (hI : B.Inv m) :
    rd m (uOrder + B.p) 8 = 1 ∧ rd m (uContext + B.p) 8 = B.wid ∧ rd m (B.p + 8) 8 = 0 ∧
    B.wid ≠ rd m currentA 8 ∧ Chain m (rd m B.wid 8) B.hs ∧
    ∀ h ∈ B.hs, rd m (h + 8) 1 = rd B.m0 (h + 8) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inr (by simp [uOrder]; bv_omega)), hB.order]
  · rw [B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inr (by simp [uContext]; bv_omega)), hB.context]
  · rw [B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inl (by bv_omega)), hB.state]
  · rw [B.rd_eq hI _ 8 fun i hi => Or.inr (Or.inl (by bv_omega))]
    exact hB.notCurrent
  · rw [B.rd_eq hI _ 8 fun i hi => Or.inr (Or.inr (Or.inl (by bv_omega)))]
    exact chain_congr hB.chain fun h hh =>
      B.rd_eq hI h 8 fun i hi => Or.inr (Or.inr (Or.inr ⟨h, hh, by bv_omega⟩))
  · intro h hh
    exact B.rd_eq hI _ 1 fun i hi => Or.inr (Or.inr (Or.inr ⟨h, hh, by bv_omega⟩))

/-- A word whose writes miss the support keeps the invariant. -/
theorem Box.inv_frame {W : Cell → Cell → Prop} (hW : ∀ a, B.supp a → ¬ W B.p a) {m' : Mem}
    (hI : B.Inv m) (h : ∀ a, ¬ W B.p a → m' a = m a) : B.Inv m' :=
  fun a ha => (h a (hW a ha)).trans (hI a ha)

theorem Box.supp_toin (hB : B.Ok) : ∀ a, B.supp a → ¬ toinCell B.p a := by
  intro a ha
  rcases ha with h | h
  · simp only [Box.userSupp, toinCell, baseCell] at h ⊢
    bv_omega
  · have := hB.apart a h
    simp only [toinCell, baseCell]
    bv_omega

theorem Box.supp_base (hB : B.Ok) : ∀ a, B.supp a → ¬ baseCell B.p a := by
  intro a ha
  rcases ha with h | h
  · simp only [Box.userSupp, toinCell, baseCell] at h ⊢
    bv_omega
  · have := hB.apart a h
    simp only [toinCell, baseCell]
    bv_omega

/-- Writes nothing. -/
abbrev noCell (_ _ : Cell) : Prop := False

theorem Box.supp_none : ∀ a, B.supp a → ¬ noCell B.p a := fun _ _ h => h

end

/-! ## What the words INTERPRET calls leave on the stack -/

set_option hygiene false in
/-- Run a word on each stack shape it might meet (on `s`, given `h`). -/
macro "shape" : tactic =>
  `(tactic| (rcases s with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩, rs, m, u, e⟩ <;>
             simp [forth, S.fail] at h ⊢ <;> (try subst h) <;> simp_all))

theorem twodup_shape (s s' : S) (h : Words.«2dup» s = .ok s') : ∃ a b t, s'.ds = a :: b :: t := by shape
theorem nip_shape (s s' : S) (h : Words.«nip» s = .ok s') :
    ∃ a b t, s.ds = a :: b :: t ∧ s'.ds = a :: t := by shape
theorem qdup_shape (s s' : S) (h : Words.«?dup» s = .ok s') :
    ∃ x t, s.ds = x :: t ∧ s'.ds = (if x = 0 then x :: t else x :: x :: t) := by
  rcases s with ⟨_ | ⟨x, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · refine ⟨x, t, rfl, ?_⟩
    by_cases hx : x = 0#64 <;> simp [forth, hx] at h <;> subst h <;> simp [hx]
theorem compile_only_shape (s s' : S) (h : Words.«compile-only?» s = .ok s') :
    ∃ x y t, s.ds = x :: t ∧ s'.ds = y :: t := by shape
theorem immediate_shape (s s' : S) (h : Words.«immediate?» s = .ok s') :
    ∃ x y t, s.ds = x :: t ∧ s'.ds = y :: t := by shape
theorem name_xt_shape (s s' : S) (h : Words.«name>xt» s = .ok s') :
    ∃ nt t, s.ds = nt :: t ∧ s'.ds = Box.xtOf s.mem nt :: t := by shape <;> rfl
theorem throw_shape (s s' : S) (h : throwM s = .ok s') : s.ds.head? = some 0 := by
  rcases s with ⟨_ | ⟨x, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · by_cases hx : x = 0#64
    · simp [hx]
    · simp [forth, hx] at h
theorem undefined_fails (s s' : S) (h : Words.«undefined» s = .ok s') : False := by
  rcases s with ⟨_ | ⟨x, _ | ⟨y, t⟩⟩, rs, m, u, e⟩ <;> simp [forth, S.fail] at h

theorem errname_frame (W) : Frame W Words.«errname#2» :=
  thread_frame (by simp only [Words.«errname#2».code]; frames [Prim.upfetch_frame, Prim.plus_frame])

theorem or_ne_zero (a b : Cell) (h : a ≠ 0) : b ||| a ≠ 0 := by bv_decide

/-! ## The invariant

INTERPRET's thread, by index (Words/Interpreter.lean): 0 PARSE-NAME, 2 to 47
at the end of the line, 4 FIND-NAME, 6 to 34 for a number; 7 to 18 throw -14
for a compile-only word; 21 to 27 test IMMEDIATE? and STATE, 28 NAME>XT,
29 EXECUTE, 31 and 32 compile; 35 NUMBER?, 38 UNDEFINED, 41 to 44 compile a
literal when STATE is set; 45 ?STACK, 46 back to 0. -/

/-- Item i on the stack is one of the sandbox's headers. -/
def At (B : Box) (i : Nat) (ds : List Cell) : Prop := ∃ x, ds[i]? = some x ∧ x ∈ B.hs

/-- What each point of the thread knows of the stack: the header FIND-NAME
returns is tracked to NAME>XT and EXECUTE; STATE is 0, so the compiling
branches (31, 32, 44) are never reached; at 18 THROW has -14. -/
def R (B : Box) : Nat → List Cell → Prop
  | 4, ds => ∃ u a t, ds = u :: a :: t
  | 5, ds => ∃ x t, ds = x :: t ∧ (x = 0 ∨ x ∈ B.hs)
  | 6, ds => (∃ t, ds = 0 :: t) ∨ ∃ x t, x ∈ B.hs ∧ ds = x :: x :: t
  | 7, ds | 19, ds | 20, ds | 21, ds | 28, ds => At B 0 ds
  | 8, ds | 9, ds | 10, ds | 13, ds | 22, ds | 23, ds => At B 1 ds
  | 11, ds | 12, ds => At B 2 ds
  | 24, ds => At B 2 ds ∧ ds.head? = some (B.p + 8)
  | 25, ds => At B 2 ds ∧ ds.head? = some 0
  | 26, ds => At B 2 ds ∧ ∀ x, ds.head? = some x → x ≠ 0
  | 27, ds => At B 1 ds ∧ ∀ x, ds.head? = some x → x ≠ 0
  | 29, ds => ∃ xt t, ds = xt :: t ∧ B.Allowed xt
  | 31, _ | 32, _ | 44, _ => False
  | 18, ds => ds.head? = some 18446744073709551602
  | 42, ds => ds.head? = some (B.p + 8)
  | 43, ds => ds.head? = some 0
  | _, _ => True

/-- The invariant: the user area and the support as they were (except while
throwing -14, at 17 and 18), and what `R` knows of the stack. -/
def Q (B : Box) (pc : Nat) (s : S) : Prop :=
  (pc ≠ 17 ∧ pc ≠ 18 → s.up = B.p ∧ B.Inv s.mem) ∧ R B pc s.ds

section
variable {B : Box}

theorem kf {pc : Nat} {f : Sem} {W : Cell → Cell → Prop} (hf : Frame W f) (hW : ∀ a, B.supp a → ¬ W B.p a)
    (hpc : pc ≠ 17 ∧ pc ≠ 18)
    (hR : ∀ s s', s.up = B.p → B.Inv s.mem → R B pc s.ds → f s = .ok s' → R B (pc + 1) s'.ds) :
    Keeps (Q B) pc (.call f) := by
  intro s pc' s' ⟨hb, hr⟩ hs
  cases hs with
  | call h =>
    obtain ⟨hu, hI⟩ := hb hpc
    obtain ⟨hu', hm⟩ := hf _ _ h
    exact ⟨fun _ => ⟨hu'.trans hu, B.inv_frame hW hI fun a ha => hm a (by rw [hu]; exact ha)⟩,
      hR s s' hu hI hr h⟩

theorem kl {pc : Nat} {v : Cell} (hpc : pc + 1 ≠ 17 ∧ pc + 1 ≠ 18 → pc ≠ 17 ∧ pc ≠ 18)
    (hR : ∀ ds, R B pc ds → R B (pc + 1) (v :: ds)) : Keeps (Q B) pc (.lit v) := by
  intro s pc' s' ⟨hb, hr⟩ hs
  cases hs with
  | lit => exact ⟨fun h => hb (hpc h), hR _ hr⟩

theorem kb {pc t : Nat} (hpc : t ≠ 17 ∧ t ≠ 18 → pc ≠ 17 ∧ pc ≠ 18) (hR : ∀ ds, R B pc ds → R B t ds) :
    Keeps (Q B) pc (.branch t) := by
  intro s pc' s' ⟨hb, hr⟩ hs
  cases hs with
  | branch => exact ⟨fun h => hb (hpc h), hR _ hr⟩

theorem kz {pc t : Nat} (hpc : pc ≠ 17 ∧ pc ≠ 18) (hj : ∀ ds, R B pc (0 :: ds) → R B t ds)
    (hn : ∀ x ds, x ≠ 0 → R B pc (x :: ds) → R B (pc + 1) ds) : Keeps (Q B) pc (.zbranch t) := by
  intro s pc' s' ⟨hb, hr⟩ hs
  cases hs with
  | zjump hds => rw [hds] at hr; exact ⟨fun _ => hb hpc, hj _ hr⟩
  | zfall hds hx => rw [hds] at hr; exact ⟨fun _ => hb hpc, hn _ _ hx hr⟩

theorem ke {pc : Nat} : Keeps (Q B) pc .exit := by
  intro s pc' s' _ hs
  cases hs

/-- A point the thread never reaches. -/
theorem kF {pc : Nat} {i : Ins} (h : ∀ ds, ¬ R B pc ds) : Keeps (Q B) pc i :=
  fun _ _ _ ⟨_, hr⟩ _ => absurd hr (h _)

set_option hygiene false in
/-- `R` across a primitive, computed on each stack shape. -/
macro "rp" : tactic =>
  `(tactic| (intro s s' hu hI hr h; rcases s with ⟨ds, rs, m, u, e⟩; simp only at hu hI hr; subst hu;
             rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [forth, S.fail] at h <;> subst h <;>
             simp_all [R, At]))

theorem k4 (hB : B.Ok) : Keeps (Q B) 4 (.call Words.«find-name») := by
  intro s _ s' ⟨hb, hr⟩ hs
  cases hs with
  | call h =>
    obtain ⟨hu, hI⟩ := hb (by decide)
    obtain ⟨h1, h2, _, hcur, hc, _⟩ := B.facts hB hI
    rcases s with ⟨ds, rs, m, p, e⟩
    obtain ⟨u, a, t, hds⟩ := hr
    simp only at hds hu hI h1 h2 hcur hc
    subst hds hu
    obtain ⟨x, hx, hfn⟩ := find_name_one u a B.wid t rs m B.p e B.hs h1 h2 hcur hc
    rw [hfn] at h
    cases h
    exact ⟨fun _ => ⟨rfl, hI⟩, ⟨x, t, rfl, hx⟩⟩

theorem k5 : Keeps (Q B) 5 (.call Words.«?dup») := by
  refine kf (qdup_frame noCell) Box.supp_none (by decide) fun s s' _ _ hr h => ?_
  obtain ⟨x, t, hds, hds'⟩ := qdup_shape s s' h
  obtain ⟨x', t', hds2, hx⟩ := hr
  rw [hds] at hds2
  cases hds2
  rw [hds']
  by_cases hx0 : x = 0
  · simp only [hx0, if_true]
    exact Or.inl ⟨t, rfl⟩
  · simp only [hx0, if_false]
    exact Or.inr ⟨x, t, hx.resolve_left hx0, rfl⟩

theorem k6 : Keeps (Q B) 6 (.zbranch 34) := by
  refine kz (by decide) (fun _ _ => trivial) fun x ds hx hr => ?_
  rcases hr with ⟨t, ht⟩ | ⟨y, t, hy, ht⟩
  · exact absurd (List.cons.inj ht).1 hx
  · exact ⟨y, by simp [(List.cons.inj ht).2], hy⟩

theorem top_at {f : Sem} (hshape : ∀ s s', f s = .ok s' → ∃ x y t, s.ds = x :: t ∧ s'.ds = y :: t)
    {i : Nat} (s s' : S) (hr : At B (i + 1) s.ds) (h : f s = .ok s') : At B (i + 1) s'.ds := by
  obtain ⟨x, y, t, h1, h2⟩ := hshape s s' h
  rw [h1] at hr
  rw [h2]
  exact hr

theorem nip_at (s s' : S) (hr : At B 0 s.ds) (h : Words.«nip» s = .ok s') : At B 0 s'.ds := by
  obtain ⟨a, b, t, h1, h2⟩ := nip_shape s s' h
  rw [h1] at hr
  rw [h2]
  exact hr

theorem k28 (hB : B.Ok) : Keeps (Q B) 28 (.call Words.«name>xt») := by
  refine kf (name_xt_frame noCell) Box.supp_none (by decide) fun s s' _ hI hr h => ?_
  obtain ⟨nt, t, h1, h2⟩ := name_xt_shape s s' h
  obtain ⟨x, hx, hm⟩ := hr
  rw [h1] at hx
  cases hx
  refine ⟨Box.xtOf s.mem nt, t, h2, nt, hm, ?_⟩
  simp only [Box.xtOf, (B.facts hB hI).2.2.2.2.2 nt hm]

theorem k29 (hkeep : ∀ xt s s', B.Allowed xt → s.up = B.p → B.Inv s.mem → dispatch xt s = .ok s' →
      s'.up = B.p ∧ B.Inv s'.mem) :
    Keeps (Q B) 29 (.call executeM) := by
  intro s _ s' ⟨hb, hr⟩ hs
  cases hs with
  | call h =>
    obtain ⟨hu, hI⟩ := hb (by decide)
    rcases s with ⟨ds, rs, m, p, e⟩
    obtain ⟨xt, t, hds, hA⟩ := hr
    simp only at hds hu hI
    subst hds
    exact ⟨fun _ => hkeep xt _ s' hA hu hI h, trivial⟩

theorem k18 : Keeps (Q B) 18 (.call throwM) := by
  intro s _ s' ⟨_, hr⟩ hs
  cases hs with
  | call h =>
    have := throw_shape _ _ h
    simp only [R] at hr
    rw [hr] at this
    simp at this

theorem k16 {f : Sem} : Keeps (Q B) 16 (.call f) := by
  intro s _ s' _ hs
  cases hs with
  | call _ => exact ⟨fun h => absurd rfl h.1, trivial⟩

theorem k38 : Keeps (Q B) 38 (.call Words.«undefined») := by
  intro s _ s' _ hs
  cases hs with
  | call h => exact (undefined_fails _ _ h).elim

/-- Every step of INTERPRET keeps the invariant. -/
theorem interpret_inv (hB : B.Ok)
    (hkeep : ∀ xt s s', B.Allowed xt → s.up = B.p → B.Inv s.mem → dispatch xt s = .ok s' →
      s'.up = B.p ∧ B.Inv s'.mem) :
    Invariant Words.«interpret».code (Q B) := by
  apply invariant_of_keeps
  simp only [Words.«interpret».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  have st := fun {m} (hI : B.Inv m) => (B.facts hB hI).2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 0 PARSE-NAME, 1 DUP, 2 0BRANCH
  · exact kf parse_name_frame (Box.supp_toin hB) (by decide) fun _ _ _ _ _ _ => trivial
  · exact kf (Prim.dup_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact kz (by decide) (fun _ _ => trivial) fun _ _ _ _ => trivial
  -- 3 2DUP, 4 FIND-NAME, 5 ?DUP, 6 0BRANCH
  · exact kf (twodup_frame noCell) Box.supp_none (by decide) fun s s' _ _ _ h => twodup_shape s s' h
  · exact k4 hB
  · exact k5
  · exact k6
  -- 7 to 13: STATE @ 0= OVER COMPILE-ONLY? AND 0BRANCH
  · exact kf (userAt_frame _ noCell) Box.supp_none (by decide) (by rp)
  · exact kf (Prim.fetch_frame noCell) Box.supp_none (by decide) (by rp)
  · exact kf (Prim.zequal_frame noCell) Box.supp_none (by decide) (by rp)
  · exact kf (Prim.over_frame noCell) Box.supp_none (by decide) (by rp)
  · exact kf (compile_only_frame noCell) Box.supp_none (by decide)
      fun s s' _ _ hr h => top_at (i := 1) (compile_only_shape) s s' hr h
  · exact kf (Prim.and_frame noCell) Box.supp_none (by decide) (by rp)
  · exact kz (by decide) (fun ds hr => by simpa [R, At] using hr) fun _ _ _ _ => trivial
  -- 14 to 18: throw -14
  · exact kf (Prim.drop_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact kf (errname_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact k16
  · exact kl (by decide) fun _ _ => rfl
  · exact k18
  -- 19 to 27: NIP NIP DUP IMMEDIATE? STATE @ 0= OR 0BRANCH
  · exact kf (nip_frame noCell) Box.supp_none (by decide) fun s s' _ _ hr h => nip_at s s' hr h
  · exact kf (nip_frame noCell) Box.supp_none (by decide) fun s s' _ _ hr h => nip_at s s' hr h
  · exact kf (Prim.dup_frame noCell) Box.supp_none (by decide) (by rp)
  · exact kf (immediate_frame noCell) Box.supp_none (by decide)
      fun s s' _ _ hr h => top_at (i := 0) (immediate_shape) s s' hr h
  · exact kf (userAt_frame _ noCell) Box.supp_none (by decide) (by rp)
  · exact kf (Prim.fetch_frame noCell) Box.supp_none (by decide) (by have := @st; rp)
  · exact kf (Prim.zequal_frame noCell) Box.supp_none (by decide) (by rp)
  · exact kf (Prim.or_frame noCell) Box.supp_none (by decide) (by have := or_ne_zero; rp)
  · exact kz (by decide) (fun ds hr => absurd rfl (hr.2 0 rfl)) fun x ds _ hr => by
      simpa [R, At] using hr.1
  -- 28 NAME>XT, 29 EXECUTE, 30 BRANCH, 31 and 32 compile, 33 BRANCH
  · exact k28 hB
  · exact k29 hkeep
  · exact kb (by decide) fun _ _ => trivial
  · exact kF fun _ h => h
  · exact kF fun _ h => h
  · exact kb (by decide) fun _ _ => trivial
  -- 34 to 40: a number
  · exact kf (twodup_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact kf number_frame (Box.supp_base hB) (by decide) fun _ _ _ _ _ _ => trivial
  · exact kf (Prim.zequal_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact kz (by decide) (fun _ _ => trivial) fun _ _ _ _ => trivial
  · exact k38
  · exact kf (nip_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact kf (nip_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  -- 41 to 44: STATE @ IF LITERAL
  · exact kf (userAt_frame _ noCell) Box.supp_none (by decide) (by rp)
  · exact kf (Prim.fetch_frame noCell) Box.supp_none (by decide) (by have := @st; rp)
  · exact kz (by decide) (fun _ _ => trivial) fun x ds hx hr => absurd (by simpa [R] using hr) hx
  · exact kF fun _ h => h
  -- 45 ?STACK, 46 BRANCH, 47 2DROP, 48 EXIT
  · exact kf (qstack_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact kb (by decide) fun _ _ => trivial
  · exact kf (twodrop_frame noCell) Box.supp_none (by decide) fun _ _ _ _ _ _ => trivial
  · exact ke
end

/-! ## Isolation -/

/-- EXECUTE, with what each xt does given by d. -/
def execWith (d : Cell → Sem) : Sem
  | ⟨xt :: s, r, m, u, e⟩ => d xt ⟨s, r, m, u, e⟩
  | s => s.fail .underflow

/-- **Sandbox isolation.** A task whose search order is the sandbox alone
(`Box.Ok`) executes only the sandbox's words: INTERPRET with EXECUTE replaced
by any d that agrees with it on their xts gives the same result, for any
line. Assumed: the sandbox's words keep the setting (`hkeep`). -/
theorem interpret_isolated (B : Box) (hB : B.Ok)
    (hkeep : ∀ xt s s', B.Allowed xt → s.up = B.p → B.Inv s.mem → dispatch xt s = .ok s' →
      s'.up = B.p ∧ B.Inv s'.mem)
    (d : Cell → Sem) (hd : ∀ xt, B.Allowed xt → d xt = dispatch xt)
    (s : S) (hu : s.up = B.p) (hm : s.mem = B.m0) :
    loopThread (Words.«interpret».code.set 29 (.call (execWith d))) s = Words.«interpret» s := by
  show _ = loopThread Words.«interpret».code s
  apply loopThread_congr _ _ (Q B) (interpret_inv hB hkeep) _ s
    ⟨fun _ => ⟨hu, fun a _ => by rw [hm]⟩, trivial⟩
  intro pc st hq
  by_cases h29 : pc = 29
  · subst h29
    right
    refine ⟨executeM, execWith d, rfl,
      List.getElem?_set_self (by simp [Words.«interpret».code]), ?_⟩
    obtain ⟨xt, t, hds, hA⟩ := hq.2
    rcases st with ⟨ds, rs, m, u, e⟩
    simp only at hds
    subst hds
    simp only [execWith, executeM, hd xt hA]
  · left
    simp [List.getElem?_set, Ne.symm h29]

/-! ## The sandbox as `sandbox.fs` builds it

The dump lists the sandbox wordlist's words (`«sandbox-wordlist».words`,
generated): each is EXPOSE's two cells, a call of the word it exposes and
EXIT. Those that compute keep the setting, proven here from their frames;
those that print go through the task's output vectors, and are assumed to
keep it for now (`outputWords`). -/

/-- f keeps the setting: the same user area, and the support as it was. -/
def Box.Keeps (B : Box) (f : Sem) : Prop :=
  ∀ s s', s.up = B.p → B.Inv s.mem → f s = .ok s' → s'.up = B.p ∧ B.Inv s'.mem

theorem keeps_of_frame {B : Box} {W : Cell → Cell → Prop} {f : Sem} (hf : Frame W f)
    (hW : ∀ a, B.supp a → ¬ W B.p a) : B.Keeps f := by
  intro s s' hu hI h
  obtain ⟨hu', hm⟩ := hf s s' h
  exact ⟨hu'.trans hu, B.inv_frame hW hI fun a ha => hm a (by rw [hu]; exact ha)⟩

/-- The sandbox's words that print, through the task's `'type` and `'bye`. -/
noncomputable def outputWords : List Sem :=
  [Words.«sandbox-wordlist:bye», Words.«sandbox-wordlist:words», Words.«sandbox-wordlist:.(»,
   Words.«sandbox-wordlist:."», Words.«sandbox-wordlist:spaces», Words.«sandbox-wordlist:space»,
   Words.«sandbox-wordlist:emit», Words.«sandbox-wordlist:cr», Words.«sandbox-wordlist:.s»,
   Words.«sandbox-wordlist:u.», Words.«sandbox-wordlist:.»]

/-- Every word in the sandbox keeps the setting, given that those that print do. -/
theorem sandbox_keeps {B : Box} (hB : B.Ok) (hout : ∀ f ∈ outputWords, B.Keeps f) :
    ∀ f ∈ Words.«sandbox-wordlist».words, B.Keeps f := by
  have o : ∀ {f}, f ∈ outputWords → B.Keeps f := fun h => hout _ h
  have n := fun {g : Sem} (hg : Frame noCell g) => keeps_of_frame (B := B) (wrapper_frame hg) Box.supp_none
  have t := fun {g : Sem} (hg : Frame toinCell g) => keeps_of_frame (B := B) (wrapper_frame hg) (Box.supp_toin hB)
  have b := fun {g : Sem} (hg : Frame baseCell g) => keeps_of_frame (B := B) (wrapper_frame hg) (Box.supp_base hB)
  simp only [Words.«sandbox-wordlist».words, List.forall_mem_cons]
  refine ⟨o (by simp [outputWords]), o (by simp [outputWords]), b decimal_frame, b hex_frame,
    t backslash_frame, t paren_frame, o (by simp [outputWords]), o (by simp [outputWords]),
    o (by simp [outputWords]), o (by simp [outputWords]), o (by simp [outputWords]),
    o (by simp [outputWords]), o (by simp [outputWords]), o (by simp [outputWords]),
    o (by simp [outputWords]),
    n (Prim.depth_frame _), n (twodrop_frame _), n (twodup_frame _), n (tuck_frame _), n (nip_frame _),
    n (rot_frame _), n (Prim.over_frame _), n (Prim.swap_frame _), n (Prim.drop_frame _),
    n (Prim.dup_frame _), n (Prim.uless_frame _), n (Prim.zless_frame _), n (Prim.zequal_frame _),
    n (greater_frame _), n (Prim.less_frame _), n (ne_frame _), n (Prim.equal_frame _),
    n (Prim.rshift_frame _), n (Prim.lshift_frame _), n (Prim.invert_frame _), n (Prim.xor_frame _),
    n (Prim.or_frame _), n (Prim.and_frame _), n (twostar_frame _), n (oneminus_frame _),
    n (oneplus_frame _), n (max_frame _), n (min_frame _), n (abs_frame _), n (negate_frame _),
    n (Prim.slashmod_frame _), n (mod_frame _), n (slash_frame _), n (Prim.star_frame _),
    n (Prim.minus_frame _), n (Prim.plus_frame _), fun _ h => nomatch h⟩

/-- **Sandbox isolation, for the sandbox `sandbox.fs` builds.** A task whose
search order is the sandbox alone executes only the sandbox's words, for any
line. Assumed: each header on the sandbox's chain runs one of the words the
dump found there (`hdump`, which the dumper is trusted for), and the words
that print keep the setting (`hout`). -/
theorem sandbox_isolated (B : Box) (hB : B.Ok)
    (hdump : ∀ h ∈ B.hs, ∃ f ∈ Words.«sandbox-wordlist».words, dispatch (Box.xtOf B.m0 h) = f)
    (hout : ∀ f ∈ outputWords, B.Keeps f)
    (d : Cell → Sem) (hd : ∀ xt, B.Allowed xt → d xt = dispatch xt)
    (s : S) (hu : s.up = B.p) (hm : s.mem = B.m0) :
    loopThread (Words.«interpret».code.set 29 (.call (execWith d))) s = Words.«interpret» s := by
  refine interpret_isolated B hB ?_ d hd s hu hm
  rintro xt s s' ⟨h, hh, rfl⟩ hu hI hx
  obtain ⟨f, hf, heq⟩ := hdump h hh
  rw [heq] at hx
  exact sandbox_keeps hB hout f hf s s' hu hI hx

end OS4.Isolation

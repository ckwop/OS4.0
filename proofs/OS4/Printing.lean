import OS4.Isolation
import OS4.Words.Interpreter

/-!
# The sandbox's words that print (V2)

`sandbox_isolated` assumed that the sandbox's eleven output words keep the
setting. Here they are proven to, given only that the task's two terminal
vectors do: `type`, which runs whatever `'type` holds, and `bye`, which runs
`'bye`. Those are the task's own words (the console's, or its connection's),
not the sandbox's, so they stay hypotheses.

Three kinds of word appear:

* threads whose every call keeps the setting (`thread_keeps`): `cr`, `.`,
  `.s`, `words` and most of the rest;
* words that store into their own user variables: EMIT (`emitted`) and `<#`
  (`hld`), checked instruction by instruction with what is known of the stack
  (`KQ`);
* HOLD, which writes through `hld`: its range check keeps the byte inside the
  task's `numbuf`, which `Box.Ok` places apart from the support.
-/

namespace OS4.Isolation
open OS4

section
variable {B : Box}

/-! ## Threads that keep the setting -/

/-- The setting, and what F knows of the state at each point. -/
def KQ (B : Box) (F : Nat → S → Prop) (pc : Nat) (s : S) : Prop :=
  s.up = B.p ∧ B.Inv s.mem ∧ F pc s

theorem thread_keeps_at {F : Nat → S → Prop} {code : List Ins} (h0 : ∀ s, F 0 s)
    (h : ∀ pc i, code[pc]? = some i → Keeps (KQ B F) pc i) :
    B.Keeps (thread code) ∧ B.Keeps (loopThread code) := by
  have go : ∀ n s s', s.up = B.p → B.Inv s.mem → run code n 0 s = .ok s' →
      s'.up = B.p ∧ B.Inv s'.mem := by
    intro n s s' hu hI hs
    obtain ⟨_, _, hu', hI', _⟩ := run_inv code _ (invariant_of_keeps h) n 0 s s' ⟨hu, hI, h0 _⟩ hs
    exact ⟨hu', hI'⟩
  refine ⟨fun s s' hu hI hs => go _ s s' hu hI hs, fun s s' hu hI hs => ?_⟩
  unfold loopThread at hs
  split at hs
  · exact go _ s s' hu hI hs
  · simp [S.fail] at hs

/-- A thread whose every call keeps the setting keeps it. -/
theorem thread_keeps {code : List Ins} (h : ∀ f, Ins.call f ∈ code → B.Keeps f) :
    B.Keeps (thread code) ∧ B.Keeps (loopThread code) :=
  thread_keeps_at (F := fun _ _ => True) (fun _ => trivial) fun pc i hi s pc' s' ⟨hu, hI, _⟩ hs => by
    cases hs with
    | call hf =>
      obtain ⟨hu', hI'⟩ := h _ (List.mem_of_getElem? hi) _ _ hu hI hf
      exact ⟨hu', hI', trivial⟩
    | _ => exact ⟨hu, hI, trivial⟩

section
variable {F : Nat → S → Prop} {pc : Nat}

theorem gk {f : Sem} (hf : B.Keeps f)
    (hR : ∀ s s', s.up = B.p → B.Inv s.mem → F pc s → f s = .ok s' → F (pc + 1) s') :
    Keeps (KQ B F) pc (.call f) := by
  intro s pc' s' ⟨hu, hI, hr⟩ hs
  cases hs with
  | call h =>
    obtain ⟨hu', hI'⟩ := hf s s' hu hI h
    exact ⟨hu', hI', hR s s' hu hI hr h⟩

theorem gl {v : Cell} (hR : ∀ s, F pc s → F (pc + 1) { s with ds := v :: s.ds }) :
    Keeps (KQ B F) pc (.lit v) := by
  intro s pc' s' ⟨hu, hI, hr⟩ hs
  cases hs with
  | lit => exact ⟨hu, hI, hR _ hr⟩

theorem gb {t : Nat} (hR : ∀ s, F pc s → F t s) : Keeps (KQ B F) pc (.branch t) := by
  intro s pc' s' ⟨hu, hI, hr⟩ hs
  cases hs with
  | branch => exact ⟨hu, hI, hR _ hr⟩

theorem gz {t : Nat} (hj : ∀ s ds, s.ds = 0 :: ds → F pc s → F t { s with ds := ds })
    (hn : ∀ s x ds, s.ds = x :: ds → x ≠ 0 → F pc s → F (pc + 1) { s with ds := ds }) :
    Keeps (KQ B F) pc (.zbranch t) := by
  intro s pc' s' ⟨hu, hI, hr⟩ hs
  cases hs with
  | zjump hds => exact ⟨hu, hI, hj _ _ hds hr⟩
  | zfall hds hx => exact ⟨hu, hI, hn _ _ _ hds hx hr⟩

/-- A point the thread never reaches. -/
theorem gF {i : Ins} (h : ∀ s, ¬ F pc s) : Keeps (KQ B F) pc i :=
  fun _ _ _ ⟨_, _, hr⟩ _ => absurd hr (h _)

theorem ge : Keeps (KQ B F) pc .exit := by
  intro s pc' s' _ hs
  cases hs

/-- A store into the cell at the user area plus off, which the support misses. -/
theorem gs {g : Sem} (hg : StoreAt g) {off : Cell}
    (hoff : ∀ a, B.supp a → 8 ≤ (a - (B.p + off)).toNat)
    (hat : ∀ s, F pc s → ∃ t, s.ds = (B.p + off) :: t) (hR : ∀ s, F (pc + 1) s) :
    Keeps (KQ B F) pc (.call g) := by
  intro s pc' s' ⟨hu, hI, hr⟩ hs
  cases hs with
  | call h =>
    obtain ⟨t, hds⟩ := hat _ hr
    obtain ⟨hu', hm⟩ := hg _ _ _ _ hds h
    exact ⟨hu'.trans hu, fun a ha => (hm a (hoff a ha)).trans (hI a ha), hR _⟩
end

theorem cstore_at : StoreAt Prim.cstore := by
  intro s s' a t hds h
  rcases s with ⟨ds, rs, m, u, e⟩
  simp only at hds
  subst hds
  cases t with
  | nil => simp [forth, S.fail] at h
  | cons v t =>
    simp only [forth, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, fun x hx => wr_apply_other x 1 m a v fun j hj => ?_⟩
    intro hxa
    subst hxa
    have : (BitVec.ofNat 64 j).toNat = j := by simp; omega
    simp [this] at hx
    omega

/-! ## User variables -/

/-- A user variable's word pushes its address and changes nothing else. -/
theorem uvar_ok {code : List Ins} {off : Cell}
    (hc : code = [.lit off, .call Prim.upfetch, .call Prim.plus, .exit]) (s s' : S)
    (h : thread code s = .ok s') : s' = { s with ds := (s.up + off) :: s.ds } := by
  subst hc
  rcases s with ⟨ds, rs, m, u, e⟩
  simp [forth] at h
  subst h
  simp [BitVec.add_comm]

theorem uvar_frame {code : List Ins} {off : Cell}
    (hc : code = [.lit off, .call Prim.upfetch, .call Prim.plus, .exit]) (W) : Frame W (thread code) :=
  fun s s' h => by rw [uvar_ok hc s s' h]; exact ⟨rfl, fun _ _ => rfl⟩

/-- The support misses an 8-byte user variable at off, between the cells it
holds and below the end of the user area. -/
theorem Box.supp_apart (hB : B.Ok) {off : Cell}
    (h : (16 ≤ off.toNat ∧ off.toNat + 8 ≤ 176) ∨ (184 ≤ off.toNat ∧ off.toNat + 8 ≤ 352) ∨
      (368 ≤ off.toNat ∧ off.toNat + 8 ≤ 512)) :
    ∀ a, B.supp a → 8 ≤ (a - (B.p + off)).toNat := by
  intro a ha
  rcases ha with h' | h'
  · simp only [Box.userSupp] at h'
    bv_omega
  · have := hB.apart a h'
    bv_omega

/-! ## The words that only read -/

section
variable (W : Cell → Cell → Prop)
open Prim

theorem pick_frame : Frame W pick := by
  intro s s' h
  rcases s with ⟨_ | ⟨x, ds⟩, rs, m, u, e⟩
  all_goals simp only [Prim.pick, S.fail] at h
  all_goals (repeat' split at h)
  all_goals first | (cases h; done) | (cases h; exact ⟨rfl, fun _ _ => rfl⟩)
theorem i_frame : Frame W i := by frame_prim
theorem umslashmod_frame : Frame W umslashmod := by
  intro s s' h
  rcases s with ⟨_ | ⟨d, _ | ⟨hi, _ | ⟨lo, ds⟩⟩⟩, rs, m, u, e⟩
  all_goals simp only [umslashmod, S.fail] at h
  all_goals (repeat' split at h)
  all_goals first | (cases h; done) | (cases h; exact ⟨rfl, fun _ _ => rfl⟩)
theorem current_frame : Frame W Words.«current» := pushConst_frame _ W
theorem slash_pad_frame : Frame W Words.«/pad» := pushConst_frame _ W
theorem slash_tib_frame : Frame W Words.«/tib» := pushConst_frame _ W
theorem slash_sbuf_frame : Frame W Words.«/sbuf» := pushConst_frame _ W
theorem slash_numbuf_frame : Frame W Words.«/numbuf» := pushConst_frame _ W
theorem zgreater_frame : Frame W Words.«0>» :=
  thread_frame (by simp only [Words.«0>».code]; frames [swap_frame, less_frame])
theorem hidden_frame : Frame W Words.«hidden?» :=
  thread_frame (by simp only [Words.«hidden?».code]
                   frames [cellplus_frame, cfetch_frame, pushConst_frame _, and_frame, zne_frame])
theorem wid_latest_frame : Frame W Words.«wid-latest» :=
  thread_frame (by simp only [Words.«wid-latest».code]
                   frames [dup_frame, current_frame, pushConst_frame _, fetch_frame, equal_frame, drop_frame])
theorem order_frame : Frame W Words.«#order» := uvar_frame rfl W
theorem context_frame : Frame W Words.«context» := uvar_frame rfl W
theorem hld_frame : Frame W Words.«hld» := uvar_frame rfl W
theorem emitted_frame : Frame W Words.«emitted» := uvar_frame rfl W
theorem task_buffers_frame : Frame W Words.«task-buffers» := uvar_frame rfl W
theorem pad_frame : Frame W Words.«pad» :=
  thread_frame (by simp only [Words.«pad».code]; frames [task_buffers_frame, fetch_frame])
theorem tib_frame : Frame W Words.«tib» :=
  thread_frame (by simp only [Words.«tib».code]; frames [pad_frame, slash_pad_frame, plus_frame])
theorem sbuf_frame : Frame W Words.«sbuf» :=
  thread_frame (by simp only [Words.«sbuf».code]; frames [tib_frame, slash_tib_frame, plus_frame])
theorem numbuf_frame : Frame W Words.«numbuf» :=
  thread_frame (by simp only [Words.«numbuf».code]; frames [sbuf_frame, slash_sbuf_frame, plus_frame])
theorem digit_out_frame : Frame W Words.«digit» :=
  thread_frame (by simp only [Words.«digit».code]; frames [dup_frame, greater_frame, plus_frame])
theorem num_end_frame : Frame W Words.«#>» :=
  thread_frame (by simp only [Words.«#>».code]
                   frames [twodrop_frame, hld_frame, fetch_frame, numbuf_frame, slash_numbuf_frame,
                     plus_frame, over_frame, minus_frame])

theorem parse_frame : Frame toinCell Prim.parse := by
  intro s s' h
  rcases s with ⟨_ | ⟨c, ds⟩, rs, m, p, e⟩
  · simp [forth, S.fail] at h
  · simp only [Prim.parse, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun a ha => wr_far m _ _ a (by simp only [toinCell] at ha; simp only [Prim.uToin]; omega)⟩
end

/-! ## HOLD, evaluated in pieces

Its thread is evaluated in three parts (the check, the store, the throw) and
the parts glued, as one `simp` over the whole thread builds a proof term too
deep for the kernel. -/

theorem hld_eq (s : S) : Words.«hld» s = .ok { s with ds := (184 + s.up) :: s.ds } := by
  rcases s with ⟨ds, rs, m, u, e⟩
  simp [forth]
theorem numbuf_eq (s : S) :
    Words.«numbuf» s = .ok { s with ds := (rd s.mem (176 + s.up) 8 + 256 + 256 + 256) :: s.ds } := by
  rcases s with ⟨ds, rs, m, u, e⟩
  simp [forth]
theorem plus_store_eq (a v : Cell) (t r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    Words.«+!» ⟨a :: v :: t, r, m, u, e⟩ = .ok ⟨t, r, wr m a 8 (rd m a 8 + v), u, e⟩ := by
  simp [forth]

theorem hold_run (ds rs : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«hold» ⟨ds, rs, m, p, e⟩ =
      run Words.«hold».code (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        0 ⟨ds, rs, m, p, e⟩ := rfl

/-- The check: is `hld` less one inside `numbuf`? -/
theorem hold_head (n : Nat) (ds rs : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«hold».code (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) 0 ⟨ds, rs, m, p, e⟩ =
      if BitVec.ult (rd m (184 + p) 8 - (rd m (176 + p) 8 + 256 + 256 + 256) - 1) 128 = true
      then run Words.«hold».code n 11 ⟨ds, rs, m, p, e⟩
      else run Words.«hold».code n 9 ⟨ds, rs, m, p, e⟩ := by
  simp [forth, ↓hld_eq, ↓numbuf_eq]

set_option simprocs false in
/-- Inside: step `hld` down and store the character there. -/
theorem hold_tail (n : Nat) (c : Cell) (t rs : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«hold».code (n + 1 + 1 + 1 + 1 + 1 + 1 + 1) 11 ⟨c :: t, rs, m, p, e⟩ =
      .ok ⟨t, rs, wr (wr m (184 + p) 8 (rd m (184 + p) 8 + 18446744073709551615))
        (rd m (184 + p) 8 + 18446744073709551615) 1 c, p, e⟩ := by
  simp only [run, Words.«hold».code, List.getElem?_cons_succ, List.getElem?_cons_zero, hld_eq,
    plus_store_eq, Prim.fetch, Prim.cstore, rd_wr_same]

set_option simprocs false in
theorem hold_tail_nil (n : Nat) (rs : List Cell) (m : Mem) (p : Cell) (e : Nat) (s' : S) :
    run Words.«hold».code (n + 1 + 1 + 1 + 1 + 1 + 1 + 1) 11 ⟨[], rs, m, p, e⟩ ≠ .ok s' := by
  simp only [run, Words.«hold».code, List.getElem?_cons_succ, List.getElem?_cons_zero, hld_eq,
    plus_store_eq, Prim.fetch, Prim.cstore, rd_wr_same, S.fail]
  intro h
  cases h

/-- Outside: throw -17. -/
theorem hold_throw (n : Nat) (ds rs : List Cell) (m : Mem) (p : Cell) (e : Nat) (s' : S) :
    run Words.«hold».code (n + 1 + 1 + 1) 9 ⟨ds, rs, m, p, e⟩ ≠ .ok s' := by
  simp [forth]

/-- HOLD with a character on the stack, if it returns: `hld` less one was
inside `numbuf`, and HOLD stepped it down and stored the character there. -/
theorem hold_ok (c : Cell) (t rs : List Cell) (m : Mem) (p : Cell) (e : Nat) (s' : S)
    (h : Words.«hold» ⟨c :: t, rs, m, p, e⟩ = .ok s') :
    (rd m (184 + p) 8 - (rd m (176 + p) 8 + 256 + 256 + 256) - 1).toNat < 128 ∧
    s' = ⟨t, rs, wr (wr m (184 + p) 8 (rd m (184 + p) 8 + 18446744073709551615))
      (rd m (184 + p) 8 + 18446744073709551615) 1 c, p, e⟩ := by
  rw [hold_run, hold_head] at h
  split at h
  · rename_i hc
    rw [hold_tail] at h
    cases h
    exact ⟨by simpa [BitVec.ult] using hc, rfl⟩
  · exact absurd h (hold_throw _ _ _ _ _ _ _)

theorem hold_nil (rs : List Cell) (m : Mem) (p : Cell) (e : Nat) (s' : S)
    (h : Words.«hold» ⟨[], rs, m, p, e⟩ = .ok s') : False := by
  rw [hold_run, hold_head] at h
  split at h
  · exact hold_tail_nil _ _ _ _ _ _ h
  · exact hold_throw _ _ _ _ _ _ _ h

/-! ## The words that print -/

/-- Writes nothing, so keeps the setting. -/
theorem nk {f : Sem} (hf : Frame noCell f) : B.Keeps f := keeps_of_frame hf Box.supp_none

/-- Calls its one word. -/
theorem wrapper_keeps {g : Sem} (hg : B.Keeps g) : B.Keeps (thread [.call g, .exit]) :=
  (thread_keeps fun f hf => by
    simp only [List.mem_cons, Ins.call.injEq, reduceCtorEq, List.mem_nil_iff, or_false] at hf
    subst hf
    exact hg).1

/-- Discharge `∀ f, .call f ∈ code → B.Keeps f` from the callees' Keeps: one
goal per call, each closed by the first lemma that fits. (Splitting by
substitution instead leaves equations between primitives, such as
`um/mod = @`, which Lean tries to decide by running them.) -/
syntax "keeping" "[" term,* "]" : tactic
macro_rules
  | `(tactic| keeping [$ls,*]) =>
    `(tactic| (simp only [List.mem_cons, List.mem_nil_iff, Ins.call.injEq, reduceCtorEq, or_false,
                 false_or, forall_eq_or_imp, forall_eq];
               (repeat' apply And.intro) <;> first $[| with_reducible exact $(ls.getElems)]*))

section
variable (hB : B.Ok)
include hB

/-- `<#`: point `hld` at the end of `numbuf`. -/
theorem begin_num_keeps : B.Keeps Words.«<#» := by
  refine (thread_keeps_at (F := fun pc s => pc = 4 → ∃ t, s.ds = (B.p + 184) :: t)
    (fun _ h => absurd h (by decide)) ?_).1
  simp only [Words.«<#».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨gk (nk (numbuf_frame _)) (fun _ _ _ _ _ _ h => absurd h (by decide)),
    gk (nk (slash_numbuf_frame _)) (fun _ _ _ _ _ _ h => absurd h (by decide)),
    gk (nk (Prim.plus_frame _)) (fun _ _ _ _ _ _ h => absurd h (by decide)),
    gk (nk (hld_frame _)) fun s s' hu _ _ h _ => ?_,
    gs store_at (Box.supp_apart hB (by decide)) (fun s h => h rfl) (fun _ h => absurd h (by decide)), ge⟩
  rw [uvar_ok rfl s s' h, hu]
  exact ⟨s.ds, rfl⟩

/-- HOLD: one step down `hld`, and the byte there, which its range check keeps
inside the task's `numbuf`, apart from the support (`Box.Ok.bufs`). -/
theorem hold_keeps : B.Keeps Words.«hold» := by
  intro s s' hu hI h
  rcases s with ⟨_ | ⟨c, t⟩, rs, m, p, e⟩
  · exact (hold_nil _ _ _ _ _ h).elim
  simp only at hu hI
  subst hu
  obtain ⟨hc, rfl⟩ := hold_ok c t rs m B.p e s' h
  refine ⟨rfl, fun a ha => ?_⟩
  have hnb : rd m (176 + B.p) 8 = rd B.m0 (B.p + 176) 8 := by
    rw [B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inr (by bv_omega)), BitVec.add_comm]
  rw [hnb] at hc
  have hA := Box.supp_apart hB (off := 184) (by decide) a ha
  have hbuf := hB.bufs a ha
  generalize rd m (184 + B.p) 8 = x at hc ⊢
  generalize rd B.m0 (B.p + 176) 8 = nb at hc hbuf
  have h1 : wr (wr m (184 + B.p) 8 (x + 18446744073709551615)) (x + 18446744073709551615) 1 c a =
      wr m (184 + B.p) 8 (x + 18446744073709551615) a :=
    wr_apply_other a 1 _ _ _ fun j hj hxa => by subst hxa; bv_omega
  have h2 : wr m (184 + B.p) 8 (x + 18446744073709551615) a = m a :=
    wr_apply_other a 8 _ _ _ fun j hj hxa => by subst hxa; bv_omega
  dsimp only
  rw [h1, h2]
  exact hI a ha

theorem digits_keeps : B.Keeps Words.«#» :=
  (thread_keeps (by
    simp only [Words.«#».code]
    simp only [List.mem_cons, List.mem_nil_iff, Ins.call.injEq, reduceCtorEq, or_false, false_or,
      forall_eq_or_imp, forall_eq]
    exact ⟨nk (userAt_frame _ _), nk (Prim.fetch_frame _), nk (umslashmod_frame _), nk (Prim.tor_frame _),
      nk (userAt_frame _ _), nk (Prim.fetch_frame _), nk (umslashmod_frame _), nk (Prim.rfrom_frame _),
      nk (rot_frame _), nk (digit_out_frame _), hold_keeps hB⟩)).1
theorem digits_all_keeps : B.Keeps Words.«#s» :=
  (thread_keeps (by
    simp only [Words.«#s».code]
    keeping [digits_keeps hB, nk (twodup_frame _), nk (Prim.or_frame _), nk (Prim.zequal_frame _)])).2
theorem sign_keeps : B.Keeps Words.«sign» :=
  (thread_keeps (by
    simp only [Words.«sign».code]
    keeping [nk (Prim.zless_frame _), hold_keeps hB])).1
theorem num_string_keeps : B.Keeps Words.«(.)» :=
  (thread_keeps (by
    simp only [Words.«(.)».code]
    keeping [nk (Prim.dup_frame _), nk (Prim.tor_frame _), nk (abs_frame _), begin_num_keeps hB,
      digits_all_keeps hB, nk (Prim.rfrom_frame _), sign_keeps hB, nk (num_end_frame _)])).1

variable (htype : B.Keeps Words.«type»)
include htype

/-- EMIT: store the character in `emitted`, then type it. -/
theorem emit_keeps : B.Keeps Words.«emit#2» := by
  refine (thread_keeps_at (F := fun pc s => pc = 1 → ∃ t, s.ds = (B.p + 168) :: t)
    (fun _ h => absurd h (by decide)) ?_).1
  simp only [Words.«emit#2».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨gk (nk (emitted_frame _)) fun s s' hu _ _ h _ => ?_,
    gs cstore_at (Box.supp_apart hB (by decide)) (fun s h => h rfl) (fun _ h => absurd h (by decide)),
    gk (nk (emitted_frame _)) (fun _ _ _ _ _ _ h => absurd h (by decide)),
    gl (fun _ _ h => absurd h (by decide)), gk htype (fun _ _ _ _ _ _ h => absurd h (by decide)), ge⟩
  rw [uvar_ok rfl s s' h, hu]
  exact ⟨s.ds, rfl⟩

theorem cr_keeps : B.Keeps Words.«cr» :=
  (thread_keeps (by
    simp only [Words.«cr».code]
    keeping [emit_keeps hB htype])).1
theorem space_keeps : B.Keeps Words.«space» :=
  (thread_keeps (by
    simp only [Words.«space».code]
    keeping [nk (bl_frame _), emit_keeps hB htype])).1
theorem spaces_keeps : B.Keeps Words.«spaces» :=
  (thread_keeps (by
    simp only [Words.«spaces».code]
    keeping [nk (Prim.dup_frame _), nk (zgreater_frame _), space_keeps hB htype,
      nk (oneminus_frame _), nk (Prim.drop_frame _)])).2
theorem dot_keeps : B.Keeps Words.«.» :=
  (thread_keeps (by
    simp only [Words.«.».code]
    keeping [num_string_keeps hB, htype, space_keeps hB htype])).1
theorem udot_keeps : B.Keeps Words.«u.» :=
  (thread_keeps (by
    simp only [Words.«u.».code]
    keeping [begin_num_keeps hB, digits_all_keeps hB, nk (num_end_frame _), htype,
      space_keeps hB htype])).1
theorem dots_keeps : B.Keeps Words.«.s» :=
  (thread_keeps (by
    simp only [Words.«.s».code]
    keeping [emit_keeps hB htype, nk (Prim.depth_frame _), begin_num_keeps hB, digits_all_keeps hB,
      nk (num_end_frame _), htype, space_keeps hB htype, nk (i_frame _), nk (Prim.minus_frame _),
      nk (oneminus_frame _), nk (pick_frame _), dot_keeps hB htype])).2
theorem words_keeps : B.Keeps Words.«words» :=
  (thread_keeps (by
    simp only [Words.«words».code]
    keeping [nk (order_frame _), nk (Prim.fetch_frame _), nk (Prim.zequal_frame _), nk (context_frame _),
      nk (wid_latest_frame _), nk (qdup_frame _), nk (Prim.dup_frame _), nk (hidden_frame _),
      nk (name_string_frame _), htype, space_keeps hB htype, cr_keeps hB htype])).2
theorem dot_paren_keeps : B.Keeps Words.«.(» :=
  (thread_keeps (by
    simp only [Words.«.(».code]
    keeping [keeps_of_frame parse_frame (Box.supp_toin hB), htype])).1

/-- `."` outside a definition: STATE is 0, so it parses and types, and never
reaches the branch that compiles (3 to 6). -/
theorem dot_quote_keeps : B.Keeps Words.«."» := by
  refine (thread_keeps_at (F := fun pc s => (pc = 1 → ∃ t, s.ds = (B.p + 8) :: t) ∧
      (pc = 2 → ∃ t, s.ds = 0 :: t) ∧ (3 ≤ pc ∧ pc ≤ 6 → False))
    (fun _ => ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩) ?_).1
  simp only [Words.«."».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨gk (nk (userAt_frame _ _)) fun s s' hu _ _ h => ?_,
    gk (nk (Prim.fetch_frame _)) fun s s' _ hI hr h => ?_,
    gz (fun _ _ _ _ => ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩)
      (fun s x ds hds hx hr => ?_),
    gF fun _ h => h.2.2 ⟨by omega, by omega⟩, gF fun _ h => h.2.2 ⟨by omega, by omega⟩,
    gF fun _ h => h.2.2 ⟨by omega, by omega⟩, gF fun _ h => h.2.2 ⟨by omega, by omega⟩,
    gl fun _ _ => ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩,
    gk (keeps_of_frame parse_frame (Box.supp_toin hB))
      (fun _ _ _ _ _ _ => ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩),
    gk htype (fun _ _ _ _ _ _ => ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩), ge⟩
  · simp only [userAt, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ => ⟨s.ds, by rw [hu]⟩, fun h => by omega, fun h => by omega⟩
  · obtain ⟨t, hds⟩ := hr.1 rfl
    rcases s with ⟨ds, rs, m, u, e⟩
    simp only at hds hI
    subst hds
    simp only [Prim.fetch, Except.ok.injEq] at h
    subst h
    refine ⟨fun h => by omega, fun _ => ⟨t, ?_⟩, fun h => by omega⟩
    simp only [(B.facts hB hI).2.2.1]
  · obtain ⟨t, ht⟩ := hr.2.1 rfl
    rw [hds] at ht
    exact absurd (List.cons.inj ht).1 hx

/-- The sandbox's words that print keep the setting, given that the task's
`type` and `bye` do. -/
theorem output_keeps (hbye : B.Keeps Words.«bye#2») : ∀ f ∈ outputWords, B.Keeps f := by
  simp only [outputWords, List.forall_mem_cons]
  exact ⟨wrapper_keeps hbye, wrapper_keeps (words_keeps hB htype), wrapper_keeps (dot_paren_keeps hB htype),
    wrapper_keeps (dot_quote_keeps hB htype), wrapper_keeps (spaces_keeps hB htype),
    wrapper_keeps (space_keeps hB htype), wrapper_keeps (emit_keeps hB htype),
    wrapper_keeps (cr_keeps hB htype), wrapper_keeps (dots_keeps hB htype),
    wrapper_keeps (udot_keeps hB htype), wrapper_keeps (dot_keeps hB htype), fun _ h => nomatch h⟩

end
end

/-- **Sandbox isolation, given the terminal.** A task whose search order is
the sandbox alone executes only the sandbox's words, for any line. Assumed:
the dump's headers (`hdump`, as for `sandbox_isolated`), and that the task's
own `type` and `bye` keep the setting: they run its terminal's vectors. -/
theorem isolated_given_terminal (B : Box) (hB : B.Ok)
    (hdump : ∀ h ∈ B.hs, ∃ f ∈ Words.«sandbox-wordlist».words, dispatch (Box.xtOf B.m0 h) = f)
    (htype : B.Keeps Words.«type») (hbye : B.Keeps Words.«bye#2»)
    (d : Cell → Sem) (hd : ∀ xt, B.Allowed xt → d xt = dispatch xt)
    (s : S) (hu : s.up = B.p) (hm : s.mem = B.m0) :
    loopThread (Words.«interpret».code.set 29 (.call (execWith d))) s = Words.«interpret» s :=
  sandbox_isolated B hB hdump (output_keeps hB htype hbye) d hd s hu hm

end OS4.Isolation

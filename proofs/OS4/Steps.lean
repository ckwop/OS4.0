import OS4.Loops
import OS4.Memory

/-!
# Invariants of a thread

A thread's run, one instruction at a time: `Next code pc s pc' s'` says the
instruction at pc takes state s to pc' and s' without ending or failing. An
invariant `Q pc s` that every step keeps holds wherever the run goes.

`run_congr` uses one to compare two threads that differ only at some
instructions: if, wherever the invariant holds, the differing instructions do
the same thing, the two threads give the same result for any fuel. This is
how a property such as "INTERPRET executes only these xts" is stated in a
model where EXECUTE is an unknown function: replace it at that instruction by
anything that agrees on those xts, and the result does not change.
-/

namespace OS4

/-- What one instruction at pc does, when it neither ends the thread nor
fails, as `run` takes it. -/
inductive Step : Ins → Nat → S → Nat → S → Prop
  | call {pc : Nat} {f : Sem} {s s' : S} : f s = .ok s' → Step (.call f) pc s (pc + 1) s'
  | lit {pc : Nat} {v : Cell} {s : S} : Step (.lit v) pc s (pc + 1) { s with ds := v :: s.ds }
  | branch {pc t : Nat} {s : S} : Step (.branch t) pc s t s
  | zjump {pc t : Nat} {s : S} {ds : List Cell} :
      s.ds = 0 :: ds → Step (.zbranch t) pc s t { s with ds := ds }
  | zfall {pc t : Nat} {s : S} {x : Cell} {ds : List Cell} :
      s.ds = x :: ds → x ≠ 0 → Step (.zbranch t) pc s (pc + 1) { s with ds := ds }
  | qdoSkip {pc t : Nat} {s : S} {start : Cell} {ds : List Cell} :
      s.ds = start :: start :: ds → Step (.qdo t) pc s t { s with ds := ds }
  | qdoEnter {pc t : Nat} {s : S} {start limit : Cell} {ds : List Cell} :
      s.ds = start :: limit :: ds → limit ≠ start →
      Step (.qdo t) pc s (pc + 1) { s with ds := ds, rs := start :: limit :: s.rs }
  | loopEnd {pc t : Nat} {s : S} {i l : Cell} {rs : List Cell} :
      s.rs = i :: l :: rs → i + 1 = l → Step (.loop t) pc s (pc + 1) { s with rs := rs }
  | loopBack {pc t : Nat} {s : S} {i l : Cell} {rs : List Cell} :
      s.rs = i :: l :: rs → i + 1 ≠ l → Step (.loop t) pc s t { s with rs := (i + 1) :: l :: rs }
  | ploopEnd {pc t : Nat} {s : S} {k i l : Cell} {ds rs : List Cell} :
      s.ds = k :: ds → s.rs = i :: l :: rs →
      (((i - l) ^^^ (i - l + k)) &&& ((i - l) ^^^ k)).msb = true →
      Step (.ploop t) pc s (pc + 1) { s with ds := ds, rs := rs }
  | ploopBack {pc t : Nat} {s : S} {k i l : Cell} {ds rs : List Cell} :
      s.ds = k :: ds → s.rs = i :: l :: rs →
      (((i - l) ^^^ (i - l + k)) &&& ((i - l) ^^^ k)).msb = false →
      Step (.ploop t) pc s t { s with ds := ds, rs := (i + k) :: l :: rs }

/-- One step of a thread: the step its instruction at pc takes. -/
def Next (code : List Ins) (pc : Nat) (s : S) (pc' : Nat) (s' : S) : Prop :=
  ∃ i, code[pc]? = some i ∧ Step i pc s pc' s'

/-- An invariant: every step from a state where it holds reaches one where it holds. -/
def Invariant (code : List Ins) (Q : Nat → S → Prop) : Prop :=
  ∀ pc s pc' s', Q pc s → Next code pc s pc' s' → Q pc' s'

/-- What an invariant asks of one instruction. -/
def Keeps (Q : Nat → S → Prop) (pc : Nat) (i : Ins) : Prop :=
  ∀ s pc' s', Q pc s → Step i pc s pc' s' → Q pc' s'

/-- An invariant is checked instruction by instruction: rewriting with
`forall_getElem?_cons` turns this into one `Keeps` per instruction. -/
theorem invariant_of_keeps {code : List Ins} {Q : Nat → S → Prop}
    (h : ∀ pc i, code[pc]? = some i → Keeps Q pc i) : Invariant code Q := by
  intro pc s pc' s' hq ⟨i, hc, hs⟩
  exact h pc i hc s pc' s' hq hs

theorem forall_getElem?_cons {α : Type} {x : α} {l : List α} {P : Nat → α → Prop} :
    (∀ pc i, (x :: l)[pc]? = some i → P pc i) ↔ P 0 x ∧ ∀ pc i, l[pc]? = some i → P (pc + 1) i := by
  constructor
  · intro h
    exact ⟨h 0 x rfl, fun pc i hi => h (pc + 1) i (by simpa using hi)⟩
  · rintro ⟨h0, h⟩ pc i hi
    cases pc with
    | zero => simp at hi; subst hi; exact h0
    | succ pc => exact h pc i (by simpa using hi)

theorem forall_getElem?_nil {α : Type} {P : Nat → α → Prop} :
    (∀ pc i, ([] : List α)[pc]? = some i → P pc i) ↔ True := by
  simp

/-- Two threads agree where Q holds: the same instruction, or calls that give
the same result. -/
def AgreeAt (code code' : List Ins) (Q : Nat → S → Prop) : Prop :=
  ∀ pc s, Q pc s → code'[pc]? = code[pc]? ∨
    ∃ f f', code[pc]? = some (.call f) ∧ code'[pc]? = some (.call f') ∧ f' s = f s

/-- The step `run` takes at pc, given the instruction there, is the same in
both threads; the rest follows by the induction hypothesis. -/
private theorem run_same_step (code code' : List Ins) (Q : Nat → S → Prop)
    (hQ : Invariant code Q) (n pc : Nat) (s : S) (hq : Q pc s)
    (ih : ∀ pc s, Q pc s → run code' n pc s = run code n pc s)
    (h : code'[pc]? = code[pc]?) :
    run code' (n + 1) pc s = run code (n + 1) pc s := by
  simp only [run, h]
  rcases hc : code[pc]? with _ | ⟨f | v | t | t | t | t | t | _⟩ <;> try dsimp only
  case some.call =>
    rcases hf : f s with e | s' <;> try dsimp only
    case ok => exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.call hf⟩)
  case some.lit => exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.lit⟩)
  case some.branch => exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.branch⟩)
  case some.zbranch =>
    rcases hds : s.ds with _ | ⟨x, ds⟩ <;> try dsimp only
    case cons =>
      by_cases hx : x = 0
      · subst hx
        rw [if_pos rfl, if_pos rfl]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.zjump hds⟩)
      · rw [if_neg hx, if_neg hx]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.zfall hds hx⟩)
  case some.qdo =>
    rcases hds : s.ds with _ | ⟨start, _ | ⟨limit, ds⟩⟩ <;> try dsimp only
    case cons.cons =>
      by_cases hl : limit = start
      · subst hl
        rw [if_pos rfl, if_pos rfl]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.qdoSkip hds⟩)
      · rw [if_neg hl, if_neg hl]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.qdoEnter hds hl⟩)
  case some.loop =>
    rcases hrs : s.rs with _ | ⟨i, _ | ⟨l, rs⟩⟩ <;> try dsimp only
    case cons.cons =>
      by_cases hl : i + 1 = l
      · rw [if_pos hl, if_pos hl]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.loopEnd hrs hl⟩)
      · rw [if_neg hl, if_neg hl]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.loopBack hrs hl⟩)
  case some.ploop =>
    rcases hds : s.ds with _ | ⟨k, ds⟩ <;> rcases hrs : s.rs with _ | ⟨i, _ | ⟨l, rs⟩⟩ <;>
      try dsimp only
    case cons.cons.cons =>
      cases hb : (((i - l) ^^^ (i - l + k)) &&& ((i - l) ^^^ k)).msb
      · simp only [hb, Bool.false_eq_true, if_false]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.ploopBack hds hrs hb⟩)
      · simp only [hb, if_true]
        exact ih _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.ploopEnd hds hrs hb⟩)

/-- Two threads that agree wherever an invariant of the first holds give the
same result, for any fuel. -/
theorem run_congr (code code' : List Ins) (Q : Nat → S → Prop)
    (hQ : Invariant code Q) (hA : AgreeAt code code' Q) :
    ∀ n pc s, Q pc s → run code' n pc s = run code n pc s := by
  intro n
  induction n with
  | zero => intro pc s _; rfl
  | succ n ih =>
    intro pc s hq
    rcases hA pc s hq with h | ⟨f, f', h, h', hf⟩
    · exact run_same_step code code' Q hQ n pc s hq ih h
    · simp only [run, h, h', hf]
      rcases hfs : f s with e | s'
      · rfl
      · exact ih _ _ (hQ _ _ _ _ hq ⟨_, h, Step.call hfs⟩)

/-- So do the loop words they define. -/
theorem loopThread_congr (code code' : List Ins) (Q : Nat → S → Prop)
    (hQ : Invariant code Q) (hA : AgreeAt code code' Q) (s : S) (hs : Q 0 s) :
    loopThread code' s = loopThread code s := by
  have h : ∀ n, run code' n 0 s = run code n 0 s := fun n => run_congr code code' Q hQ hA n 0 s hs
  by_cases ex : ∃ n, ¬ outOfFuel (run code n 0 s)
  · obtain ⟨n, hn⟩ := ex
    rw [loopThread_eq code' s n _ (h n) hn, loopThread_eq code s n _ rfl hn]
  · have ex' : ¬ ∃ n, ¬ outOfFuel (run code' n 0 s) := by simpa only [h] using ex
    unfold loopThread
    rw [dif_neg ex, dif_neg ex']

/-- A run that returns ends at an EXIT, where the invariant holds. -/
theorem run_inv (code : List Ins) (Q : Nat → S → Prop) (hQ : Invariant code Q) :
    ∀ n pc s s', Q pc s → run code n pc s = .ok s' → ∃ pe, code[pe]? = some .exit ∧ Q pe s' := by
  intro n
  induction n with
  | zero => intro pc s s' _ h; simp [run, S.fail] at h
  | succ n ih =>
    intro pc s s' hq h
    simp only [run] at h
    rcases hc : code[pc]? with _ | ⟨f | v | t | t | t | t | t | _⟩ <;> simp only [hc] at h
    case none => simp [S.fail] at h
    case some.exit => cases h; exact ⟨pc, hc, hq⟩
    case some.call =>
      rcases hf : f s with e | s1 <;> simp only [hf] at h
      case error => simp at h
      case ok => exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.call hf⟩) h
    case some.lit => exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.lit⟩) h
    case some.branch => exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.branch⟩) h
    case some.zbranch =>
      rcases hds : s.ds with _ | ⟨x, ds⟩ <;> simp only [hds] at h
      case nil => simp [S.fail] at h
      case cons =>
        by_cases hx : x = 0
        · subst hx
          rw [if_pos rfl] at h
          exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.zjump hds⟩) h
        · rw [if_neg hx] at h
          exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.zfall hds hx⟩) h
    case some.qdo =>
      rcases hds : s.ds with _ | ⟨start, _ | ⟨limit, ds⟩⟩ <;> simp only [hds] at h
      case nil => simp [S.fail] at h
      case cons.nil => simp [S.fail] at h
      case cons.cons =>
        by_cases hl : limit = start
        · subst hl
          rw [if_pos rfl] at h
          exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.qdoSkip hds⟩) h
        · rw [if_neg hl] at h
          exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.qdoEnter hds hl⟩) h
    case some.loop =>
      rcases hrs : s.rs with _ | ⟨i, _ | ⟨l, rs⟩⟩ <;> simp only [hrs] at h
      case nil => simp [S.fail] at h
      case cons.nil => simp [S.fail] at h
      case cons.cons =>
        by_cases hl : i + 1 = l
        · rw [if_pos hl] at h
          exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.loopEnd hrs hl⟩) h
        · rw [if_neg hl] at h
          exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.loopBack hrs hl⟩) h
    case some.ploop =>
      rcases hds : s.ds with _ | ⟨k, ds⟩ <;> rcases hrs : s.rs with _ | ⟨i, _ | ⟨l, rs⟩⟩ <;>
        simp only [hds, hrs] at h
      all_goals try (simp [S.fail] at h; done)
      cases hb : (((i - l) ^^^ (i - l + k)) &&& ((i - l) ^^^ k)).msb
      · simp only [hb, Bool.false_eq_true, if_false] at h
        exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.ploopBack hds hrs hb⟩) h
      · simp only [hb, if_true] at h
        exact ih _ _ _ (hQ _ _ _ _ hq ⟨_, hc, Step.ploopEnd hds hrs hb⟩) h

/-! ## Frames: what a word leaves alone

`Frame W f`: when f returns, the user area is the same, and so is every byte
outside W (given the user area). A thread whose calls all have frame W has it
too, whatever its stack does; so a word that writes nothing, or only its own
user variables, can be shown so without knowing its stack effect. -/

def Frame (W : Cell → Cell → Prop) (f : Sem) : Prop :=
  ∀ s s', f s = .ok s' → s'.up = s.up ∧ ∀ a, ¬ W s.up a → s'.mem a = s.mem a

private theorem frame_inv {W : Cell → Cell → Prop} {code : List Ins}
    (h : ∀ f, Ins.call f ∈ code → Frame W f) (s0 : S) :
    Invariant code (fun _ s => s.up = s0.up ∧ ∀ a, ¬ W s0.up a → s.mem a = s0.mem a) := by
  intro pc s pc' s' ⟨hu, hm⟩ ⟨i, hc, hs⟩
  cases hs with
  | call hf =>
    obtain ⟨hu', hm'⟩ := h _ (List.mem_of_getElem? hc) _ _ hf
    refine ⟨hu'.trans hu, fun a ha => ?_⟩
    rw [hm' a (hu ▸ ha), hm a ha]
  | _ => exact ⟨hu, hm⟩

theorem thread_frame {W : Cell → Cell → Prop} {code : List Ins}
    (h : ∀ f, Ins.call f ∈ code → Frame W f) : Frame W (thread code) := by
  intro s s' hs
  obtain ⟨_, _, hu, hm⟩ := run_inv code _ (frame_inv h s) _ 0 s s' ⟨rfl, fun _ _ => rfl⟩ hs
  exact ⟨hu, hm⟩

theorem loopThread_frame {W : Cell → Cell → Prop} {code : List Ins}
    (h : ∀ f, Ins.call f ∈ code → Frame W f) : Frame W (loopThread code) := by
  intro s s' hs
  unfold loopThread at hs
  split at hs
  · obtain ⟨_, _, hu, hm⟩ := run_inv code _ (frame_inv h s) _ 0 s s' ⟨rfl, fun _ _ => rfl⟩ hs
    exact ⟨hu, hm⟩
  · simp [S.fail] at hs

/-- Prove `Frame W p` for a primitive that writes nothing. -/
macro "frame_prim" : tactic =>
  `(tactic| (intro s s' h;
             rcases s with ⟨_ | ⟨x, _ | ⟨y, ds⟩⟩, _ | ⟨z, rs⟩, m, u, e⟩ <;>
             simp [forth, S.fail] at h <;> (repeat' split at h) <;> (try simp at h) <;>
             (subst h; exact ⟨rfl, fun _ _ => rfl⟩)))

/-- Prove `∀ f, .call f ∈ code → Frame W f` from the callees' frames, given
as lemmas taking W. -/
syntax "frames" "[" term,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| frames [$ls,*]) =>
    `(tactic| (intro f hf;
               simp only [List.mem_cons, List.mem_nil_iff, Ins.call.injEq, reduceCtorEq,
                 or_false, false_or] at hf;
               repeat' (obtain rfl | hf := hf);
               all_goals (try subst hf);
               all_goals first $[| with_reducible exact ($(ls.getElems) _)]*))

namespace Prim
theorem dup_frame (W) : Frame W dup := by frame_prim
theorem drop_frame (W) : Frame W drop := by frame_prim
theorem swap_frame (W) : Frame W swap := by frame_prim
theorem over_frame (W) : Frame W over := by frame_prim
theorem tor_frame (W) : Frame W tor := by frame_prim
theorem rfrom_frame (W) : Frame W rfrom := by frame_prim
theorem rfetch_frame (W) : Frame W rfetch := by frame_prim
theorem depth_frame (W) : Frame W depth := by frame_prim
theorem plus_frame (W) : Frame W plus := by frame_prim
theorem minus_frame (W) : Frame W minus := by frame_prim
theorem star_frame (W) : Frame W star := by frame_prim
theorem and_frame (W) : Frame W and := by frame_prim
theorem or_frame (W) : Frame W or := by frame_prim
theorem equal_frame (W) : Frame W equal := by frame_prim
theorem less_frame (W) : Frame W less := by frame_prim
theorem uless_frame (W) : Frame W uless := by frame_prim
theorem zequal_frame (W) : Frame W zequal := by frame_prim
theorem zless_frame (W) : Frame W zless := by frame_prim
theorem fetch_frame (W) : Frame W fetch := by frame_prim
theorem cfetch_frame (W) : Frame W cfetch := by frame_prim
theorem upfetch_frame (W) : Frame W upfetch := by frame_prim
end Prim

theorem userAt_frame (off : Cell) (W) : Frame W (userAt off) := by frame_prim
theorem pushConst_frame (v : Cell) (W) : Frame W (pushConst v) := by frame_prim
theorem kconst_frame (n : String) (W) : Frame W (kconst n) := by frame_prim
theorem throwM_frame (W) : Frame W throwM := by frame_prim

/-! ## Frames of words that store into their own user variables

A word such as PARSE-NAME writes `>in` with `+!`, whose address it pushes
just before with the user variable's word. Its frame is checked instruction
by instruction: at the stores (the pcs in P), the address on top is that user
variable's, and nothing else writes. -/

/-- The user area is s0's, and every byte outside W is as it was in s0. -/
def Framed (W : Cell → Cell → Prop) (s0 s : S) : Prop :=
  s.up = s0.up ∧ ∀ a, ¬ W s0.up a → s.mem a = s0.mem a

theorem framed_call {W : Cell → Cell → Prop} {f : Sem} (hf : Frame W f) {s0 s s' : S}
    (h : Framed W s0 s) (hs : f s = .ok s') : Framed W s0 s' := by
  obtain ⟨hu, hm⟩ := h
  obtain ⟨hu', hm'⟩ := hf _ _ hs
  refine ⟨hu'.trans hu, fun a ha => ?_⟩
  rw [hm' a (hu ▸ ha), hm a ha]

/-- The invariant: framed, and at a store the user variable's address on top. -/
def FQ (W : Cell → Cell → Prop) (P : List Nat) (off : Cell) (s0 : S) (pc : Nat) (s : S) : Prop :=
  Framed W s0 s ∧ (pc ∈ P → ∃ t, s.ds = (s0.up + off) :: t)

/-- g writes only the cell whose address is on top. -/
def StoreAt (g : Sem) : Prop :=
  ∀ s s' a t, s.ds = a :: t → g s = .ok s' → s'.up = s.up ∧ ∀ x, 8 ≤ (x - a).toNat → s'.mem x = s.mem x

section
variable {W : Cell → Cell → Prop} {P : List Nat} {off : Cell} {s0 : S} {pc : Nat}

theorem keeps_frame {f : Sem} (hf : Frame W f) (hp : pc + 1 ∉ P) : Keeps (FQ W P off s0) pc (.call f) := by
  intro s pc' s' ⟨h, _⟩ hs
  cases hs with
  | call h' => exact ⟨framed_call hf h h', fun h'' => absurd h'' hp⟩

theorem keeps_userAt : Keeps (FQ W P off s0) pc (.call (userAt off)) := by
  intro s pc' s' ⟨h, _⟩ hs
  cases hs with
  | call h' =>
    refine ⟨framed_call (userAt_frame off W) h h', fun _ => ⟨s.ds, ?_⟩⟩
    simp only [userAt, Except.ok.injEq] at h'
    subst h'
    simp [h.1]

theorem keeps_store {g : Sem} (hg : StoreAt g) (hW : ∀ p a, (a - (p + off)).toNat < 8 → W p a)
    (hin : pc ∈ P) (hp : pc + 1 ∉ P) : Keeps (FQ W P off s0) pc (.call g) := by
  intro s pc' s' ⟨⟨hu, hm⟩, ht⟩ hs
  cases hs with
  | call h' =>
    obtain ⟨t, hds⟩ := ht hin
    obtain ⟨hu', hm'⟩ := hg _ _ _ _ hds h'
    refine ⟨⟨hu'.trans hu, fun a ha => ?_⟩, fun h'' => absurd h'' hp⟩
    have : 8 ≤ (a - (s0.up + off)).toNat := by
      have := mt (hW s0.up a) ha
      omega
    rw [hm' a this, hm a ha]

theorem keeps_lit {v : Cell} (hp : pc + 1 ∉ P) : Keeps (FQ W P off s0) pc (.lit v) := by
  intro s pc' s' ⟨h, _⟩ hs
  cases hs with
  | lit => exact ⟨h, fun h'' => absurd h'' hp⟩

theorem keeps_branch {t : Nat} (ht : t ∉ P) : Keeps (FQ W P off s0) pc (.branch t) := by
  intro s pc' s' ⟨h, _⟩ hs
  cases hs with
  | branch => exact ⟨h, fun h'' => absurd h'' ht⟩

theorem keeps_zbranch {t : Nat} (ht : t ∉ P) (hp : pc + 1 ∉ P) :
    Keeps (FQ W P off s0) pc (.zbranch t) := by
  intro s pc' s' ⟨h, _⟩ hs
  cases hs with
  | zjump _ => exact ⟨h, fun h'' => absurd h'' ht⟩
  | zfall _ _ => exact ⟨h, fun h'' => absurd h'' hp⟩

theorem keeps_exit : Keeps (FQ W P off s0) pc .exit := by
  intro s pc' s' _ hs
  cases hs
end

/-- A thread whose every instruction keeps `FQ` has frame W. -/
theorem thread_frame_at {W : Cell → Cell → Prop} {P : List Nat} {off : Cell} {code : List Ins}
    (h0 : 0 ∉ P) (h : ∀ s0 pc i, code[pc]? = some i → Keeps (FQ W P off s0) pc i) :
    Frame W (thread code) ∧ Frame W (loopThread code) := by
  have go : ∀ n s s', run code n 0 s = .ok s' → s'.up = s.up ∧ ∀ a, ¬ W s.up a → s'.mem a = s.mem a := by
    intro n s s' hs
    obtain ⟨_, _, hf, _⟩ :=
      run_inv code _ (invariant_of_keeps (h s)) n 0 s s' ⟨⟨rfl, fun _ _ => rfl⟩, fun h' => absurd h' h0⟩ hs
    exact hf
  refine ⟨fun s s' hs => go _ s s' hs, fun s s' hs => ?_⟩
  unfold loopThread at hs
  split at hs
  · exact go _ s s' hs
  · simp [S.fail] at hs

/-- Discharge each instruction's `Keeps` after `forall_getElem?_cons` has
split them out: stores through `stores`, other calls through `frames`. -/
syntax "keeps" "[" term,* "]" "[" term,* "]" : tactic
macro_rules
  | `(tactic| keeps [$fs,*] [$gs,*]) =>
    `(tactic| (repeat' apply And.intro) <;>
       first
       | with_reducible exact keeps_exit
       | ((with_reducible apply keeps_lit); decide)
       | ((with_reducible apply keeps_branch); decide)
       | ((with_reducible apply keeps_zbranch) <;> decide)
       | with_reducible exact keeps_userAt
       $[| ((with_reducible apply keeps_frame ($(fs.getElems) _)); decide)]*
       $[| ((with_reducible apply keeps_store $(gs.getElems) (fun _ _ h => h)) <;> decide)]*)

theorem store_at : StoreAt Prim.store := by
  intro s s' a t hds h
  rcases s with ⟨ds, rs, m, u, e⟩
  simp only at hds
  subst hds
  cases t with
  | nil => simp [forth, S.fail] at h
  | cons v t =>
    simp only [forth, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, fun x hx => wr_apply_other x 8 m a v fun j hj => ?_⟩
    intro hxa
    subst hxa
    have : (BitVec.ofNat 64 j).toNat = j := by simp; omega
    simp [this] at hx
    omega

end OS4

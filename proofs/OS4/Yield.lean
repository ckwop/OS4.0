import OS4.Machine

/-!
# Yielding: steps between pauses

The watchdog stops a task that runs too long without pausing (tasks.fs;
DECISIONS.md #48–56). Here a task's run is counted in Forth instructions:
each cell of a thread executed is one step, a primitive included, and PAUSE
gives the task its whole allowance again. A word that would take a step with
none left is stopped (`OutT.watchdog`).

This is a second semantics of the same threads, beside `Sem`:
tools/forth2lean.py generates both from the same dump. A word's `Cost` says
how many steps it may take before it first pauses, and how many between and
after pauses; `threadT_cost` proves it from a certificate checked by
`decide`, given its callees' Costs, as `thread_spec` does for stack effects.

Counted: thread cells. A primitive is one step however long its assembly runs
(`cmove`, `fill` and `sha256-block` loop inside). Words the generator is told
not to count (proofs/yields.txt) run in no steps at all: each is a loop
without a pause, whose bound needs more than this file proves.
-/

namespace OS4

/-- The watchdog's allowance: Forth instructions a task may run between two
pauses. Unknown here: each theorem says how large it must be. -/
opaque allowance : Nat

/-- How a counted run ends: as `Sem` would, with the steps left; or stopped by
the watchdog. A failure keeps its steps left, as CATCH carries on from it. -/
inductive OutT where
  | ok (s : S) (left : Nat)
  | fail (f : Fail) (left : Nat)
  | watchdog

/-- A word, counted: from a state and the steps left. -/
abbrev SemT := S → Nat → OutT

def S.failT (s : S) (e : Err) (b : Nat) : OutT := .fail ⟨e, s.mem, s.ext⟩ b

inductive InsT where
  | call (f : SemT)
  | lit (v : Cell)
  | branch (t : Nat)
  | zbranch (t : Nat)
  | qdo (t : Nat)
  | loop (t : Nat)
  | ploop (t : Nat)
  | exit

/-- `run`, taking one step per cell. -/
def runT (code : List InsT) : Nat → Nat → S → Nat → OutT
  | 0, _, s, b => s.failT .fuel b
  | n + 1, pc, s, b =>
    match b with
    | 0 => .watchdog
    | b + 1 =>
    match code[pc]? with
    | none => s.failT .badBranch b
    | some .exit => .ok s b
    | some (.call f) =>
      match f s b with
      | .ok s' b' => runT code n (pc + 1) s' b'
      | .fail e b' => .fail e b'
      | .watchdog => .watchdog
    | some (.lit v) => runT code n (pc + 1) { s with ds := v :: s.ds } b
    | some (.branch t) => runT code n t s b
    | some (.zbranch t) =>
      match s.ds with
      | x :: ds => if x = 0 then runT code n t { s with ds := ds } b
                   else runT code n (pc + 1) { s with ds := ds } b
      | [] => s.failT .underflow b
    | some (.qdo t) =>
      match s.ds with
      | start :: limit :: ds =>
        if limit = start then runT code n t { s with ds := ds } b
        else runT code n (pc + 1) { s with ds := ds, rs := start :: limit :: s.rs } b
      | _ => s.failT .underflow b
    | some (.loop t) =>
      match s.rs with
      | i :: l :: rs =>
        if i + 1 = l then runT code n (pc + 1) { s with rs := rs } b
        else runT code n t { s with rs := (i + 1) :: l :: rs } b
      | _ => s.failT .rUnderflow b
    | some (.ploop t) =>
      match s.ds, s.rs with
      | k :: ds, i :: l :: rs =>
        let d := i - l
        if ((d ^^^ (d + k)) &&& (d ^^^ k)).msb then runT code n (pc + 1) { s with ds := ds, rs := rs } b
        else runT code n t { s with ds := ds, rs := (i + k) :: l :: rs } b
      | [], _ => s.failT .underflow b
      | _, _ => s.failT .rUnderflow b

def OutT.outOfFuel : OutT → Prop
  | .fail f _ => f.err = .fuel
  | _ => False

/-- A colon definition, counted: its outcome if it ends or is stopped, else
`fuel` (it runs for ever, pausing). -/
noncomputable def threadT (code : List InsT) : SemT := fun s b =>
  open Classical in
  if h : ∃ n, ¬ (runT code n 0 s b).outOfFuel then runT code (Classical.choose h) 0 s b
  else s.failT .fuel b

/-- A word that takes no steps of its own beyond the cell that calls it: a
primitive, a constant, or a word not counted. -/
def liftT (f : Sem) : SemT := fun s b =>
  match f s with
  | .ok s' => .ok s' b
  | .error e => .fail e b

/-- PAUSE: the task has its whole allowance again. -/
def pauseT : SemT := fun s _ =>
  match Prim.pause s with
  | .ok s' => .ok s' allowance
  | .error e => .fail e allowance

def doesChildT (body : Cell) (code : SemT) : SemT := fun s b => code { s with ds := body :: s.ds } b

/-- `lit xt execute`, where xt is the word f (the generator resolves it). -/
def executeT (f : SemT) : SemT := fun s b =>
  match s.ds with
  | _ :: ds => f { s with ds := ds } b
  | [] => s.failT .underflow b

/-- Which of a table's words an xt is: unknown here. -/
opaque whichOf : Cell → Nat

/-- EXECUTE of an xt from a table that holds only the words fs
(proofs/yields.txt says which). An xt outside them is `unknownXt`: the proofs
say nothing about what it would run. -/
def executeOf (fs : List SemT) : SemT := fun s b =>
  match s.ds with
  | xt :: ds =>
    match fs[whichOf xt]? with
    | some f => f { s with ds := ds } b
    | none => s.failT .unknownXt b
  | [] => s.failT .underflow b

/-- `lit xt catch`, where xt is the word f: as `catchM`. -/
def catchT (f : SemT) : SemT := fun st b =>
  match st with
  | ⟨_ :: s, r, m, u, e⟩ =>
    match f ⟨s, r, m, u, e⟩ b with
    | .ok st' b' => .ok { st' with ds := 0 :: st'.ds } b'
    | .fail fl b' =>
      match fl.err.code with
      | some n => .ok ⟨n :: (List.range s.length).map (junk fl.ext), r, fl.mem, u, fl.ext⟩ b'
      | none => .fail fl b'
    | .watchdog => .watchdog
  | s => s.failT .underflow b

/-! ## Costs -/

/-- The steps c a word has left, entered with b: within the allowance, and
either at most n spent since entry or at most m since a pause. With p, it
surely paused, so the second. -/
def Left (n m : Nat) (p : Bool) (b c : Nat) : Prop :=
  c ≤ allowance ∧ (if p = true then allowance ≤ c + m else b ≤ c + n ∨ allowance ≤ c + m)

def Post (n m : Nat) (p : Bool) (b : Nat) : OutT → Prop
  | .ok _ c => Left n m p b c
  | .fail _ c => Left n m false b c
  | .watchdog => False

/-- f is never stopped by the watchdog if it is entered with at least n steps
left and the allowance is at least m; it spends at most n before it first
pauses and at most m between or after pauses; with p it surely pauses before
it returns. -/
def Cost (f : SemT) (n m : Nat) (p : Bool) : Prop :=
  m ≤ allowance → ∀ s b, b ≤ allowance → n ≤ b → Post n m p b (f s b)

theorem left_mono {x y X Y b c : Nat} {p q : Bool} (h : Left x y p b c)
    (hx : x ≤ X) (hy : y ≤ Y) (hp : q = true → p = true) : Left X Y q b c := by
  unfold Left at *
  cases p <;> cases q <;> simp_all <;> omega

theorem left_ge {x y b c k : Nat} {p : Bool} (h : Left x y p b c)
    (hx : x + k ≤ b) (hy : y + k ≤ allowance) : k ≤ c := by
  unfold Left at h
  cases p <;> simp_all <;> omega

theorem left_tick {x y b c : Nat} {p : Bool} (h : Left x y p b (c + 1)) : Left (x + 1) (y + 1) p b c := by
  unfold Left at *
  cases p <;> simp_all <;> omega

/-- After a call that surely paused, only what it spent since counts. -/
theorem left_paused {n m b c c' : Nat} (h : Left n m true c c') : Left m m true b c' := by
  unfold Left at *
  simp_all

/-- After a call that may not have paused, its steps add to the caller's. -/
theorem left_call {x y n m X Y b c c' : Nat} {q : Bool} (hb : b ≤ allowance)
    (h1 : Left x y q b c) (h2 : Left n m false c c')
    (hx : x + n ≤ X) (hy : y + n ≤ Y) (hmx : m ≤ X) (hmy : m ≤ Y) : Left X Y q b c' := by
  unfold Left at *
  cases q <;> simp_all <;> omega

theorem left_weaken {n m b c : Nat} {p : Bool} (h : Left n m p b c) : Left n m false b c :=
  left_mono h (Nat.le_refl _) (Nat.le_refl _) (by simp)

theorem post_weaken {n m b : Nat} {p : Bool} {o : OutT} (h : Post n m p b o) : Post n m false b o := by
  cases o with
  | ok _ c => exact left_weaken h
  | fail _ c => exact h
  | watchdog => exact h

theorem liftT_cost (f : Sem) : Cost (liftT f) 0 0 false := by
  intro _ s b hb _
  have : Left 0 0 false b b := by simp [Left] <;> omega
  unfold liftT
  split <;> simpa [Post] using this

theorem pauseT_cost : Cost pauseT 0 0 true := by
  intro _ s b _ _
  simp [pauseT, Prim.pause, Post, Left]

theorem doesChildT_cost {code : SemT} {n m : Nat} {p : Bool} (v : Cell) (h : Cost code n m p) :
    Cost (doesChildT v code) n m p := by
  intro hm s b hb hn
  exact h hm _ b hb hn

theorem executeT_cost {f : SemT} {n m : Nat} {p : Bool} (h : Cost f n m p) : Cost (executeT f) n m p := by
  intro hm s b hb hn
  unfold executeT
  split
  · exact h hm _ b hb hn
  · simp [S.failT, Post, Left] <;> omega

/-- A Cost still holds with more steps allowed, or less promised. -/
theorem Cost.weaken {f : SemT} {n m N M : Nat} {p P : Bool} (h : Cost f n m p)
    (hn : n ≤ N) (hm : m ≤ M) (hp : P = true → p = true) : Cost f N M P := by
  intro hM s b hb hN
  have := h (by omega) s b hb (by omega)
  cases hr : f s b with
  | ok _ c => rw [hr] at this; exact left_mono this hn hm hp
  | fail _ c => rw [hr] at this; exact left_mono this hn hm (by simp)
  | watchdog => rw [hr] at this; exact this.elim

def AllCost : List SemT → Nat → Nat → Bool → Prop
  | [], _, _, _ => True
  | f :: fs, n, m, p => Cost f n m p ∧ AllCost fs n m p

theorem executeOf_cost {fs : List SemT} {n m : Nat} {p : Bool} (h : AllCost fs n m p) :
    Cost (executeOf fs) n m p := by
  have hget : ∀ (i : Nat) (f : SemT), fs[i]? = some f → Cost f n m p := by
    induction fs with
    | nil => intro i f hi; simp at hi
    | cons g gs ih =>
      intro i f hi
      cases i with
      | zero => simp at hi; subst hi; exact h.1
      | succ i => simp at hi; exact ih h.2 i f hi
  intro hm s b hb hn
  unfold executeOf
  split
  · split
    · rename_i f hf
      exact hget _ f hf hm _ b hb hn
    · simp [S.failT, Post, Left] <;> omega
  · simp [S.failT, Post, Left] <;> omega

theorem catchT_cost {f : SemT} {n m : Nat} {p : Bool} (h : Cost f n m p) : Cost (catchT f) n m false := by
  intro hm st b hb hn
  match st with
  | ⟨_ :: s, r, mem, u, e⟩ =>
    have hf := h hm ⟨s, r, mem, u, e⟩ b hb hn
    simp only [catchT]
    split
    · rename_i st' b' heq
      rw [heq] at hf
      exact left_weaken hf
    · rename_i fl b' heq
      rw [heq] at hf
      split <;> exact hf
    · rename_i heq
      rw [heq] at hf
      exact hf.elim
  | ⟨[], r, mem, u, e⟩ =>
    simp [catchT, S.failT, Post, Left] <;> omega

/-! ## Certificates -/

/-- Before one instruction: steps spent since entry (x) and since a pause (y)
at most, and whether a pause surely happened; for a call, the callee's Cost.
Unreachable instructions are dead. -/
structure CertT where
  live : Bool
  x : Nat
  y : Nat
  paused : Bool
  n : Nat
  m : Nat
  p : Bool

/-- Instruction q is live and its entry allows (x, y, paused). -/
def covers (cert : List CertT) (q x y : Nat) (paused : Bool) : Bool :=
  match cert[q]? with
  | some c => c.live && decide (x ≤ c.x) && decide (y ≤ c.y) && (!c.paused || paused)
  | none => false

/-- What one instruction needs after its own step, at (x, y). -/
def stepIns (code : List InsT) (cert : List CertT) (N M : Nat) (P : Bool) (pc : Nat) (c : CertT) : Bool :=
  let x := c.x + 1
  let y := c.y + 1
  match code[pc]? with
  | none => true
  | some .exit => !P || c.paused
  | some (.call _) =>
    decide (x + c.n ≤ N) && decide (y + c.n ≤ M) && decide (c.m ≤ N) && decide (c.m ≤ M) &&
    (if c.p then covers cert (pc + 1) c.m c.m true
     else covers cert (pc + 1) (x + c.n) (y + c.n) c.paused && covers cert (pc + 1) c.m c.m c.paused)
  | some (.lit _) => covers cert (pc + 1) x y c.paused
  | some (.branch t) => covers cert t x y c.paused
  | some (.zbranch t) => covers cert t x y c.paused && covers cert (pc + 1) x y c.paused
  | some (.qdo t) => covers cert t x y c.paused && covers cert (pc + 1) x y c.paused
  | some (.loop t) => covers cert t x y c.paused && covers cert (pc + 1) x y c.paused
  | some (.ploop t) => covers cert t x y c.paused && covers cert (pc + 1) x y c.paused

def stepT (code : List InsT) (cert : List CertT) (N M : Nat) (P : Bool) (pc : Nat) : Bool :=
  match cert[pc]? with
  | none => false
  | some c => !c.live || (decide (c.x + 1 ≤ N) && decide (c.y + 1 ≤ M) && stepIns code cert N M P pc c)

/-- The certificate for a word with Cost N M P. -/
def checkT (code : List InsT) (cert : List CertT) (N M : Nat) (P : Bool) : Bool :=
  covers cert 0 0 0 false && (List.range cert.length).all (stepT code cert N M P)

def InsCosts : InsT → CertT → Prop
  | .call f, c => Cost f c.n c.m c.p
  | _, _ => True

def CallsCost : List InsT → List CertT → Prop
  | [], _ => True
  | _ :: _, [] => True
  | i :: is, c :: cs => InsCosts i c ∧ CallsCost is cs

theorem callsCost {code : List InsT} {cert : List CertT} (h : CallsCost code cert) :
    ∀ {pc : Nat} {f : SemT} {c : CertT}, code[pc]? = some (.call f) → cert[pc]? = some c →
      Cost f c.n c.m c.p := by
  induction code generalizing cert with
  | nil => intro pc f c h1; simp at h1
  | cons i is ih =>
    cases cert with
    | nil => intro pc f c _ h2; simp at h2
    | cons c' cs =>
      obtain ⟨hi, hrest⟩ := h
      intro pc f c h1 h2
      cases pc with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        exact hi
      | succ pc =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih hrest h1 h2

theorem covers_spec {cert : List CertT} {q x y : Nat} {p : Bool} (h : covers cert q x y p = true) :
    ∃ c, cert[q]? = some c ∧ c.live = true ∧ x ≤ c.x ∧ y ≤ c.y ∧ (c.paused = true → p = true) := by
  unfold covers at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hl, hx⟩, hy⟩, hp⟩ := h
    refine ⟨c, hc, hl, hx, hy, fun h' => ?_⟩
    rcases hp with hp | hp
    · rw [hp] at h'; contradiction
    · exact hp
  · contradiction

/-! ## The bridge -/

/-- Running a checked thread from a live instruction, with steps left as its
certificate allows, ends as the word's Cost says: never stopped. -/
theorem runT_sound {code : List InsT} {cert : List CertT} {N M : Nat} {P : Bool} {b : Nat}
    (hc : ∀ pc, pc < cert.length → stepT code cert N M P pc = true) (hcalls : CallsCost code cert)
    (hM : M ≤ allowance) (hb : b ≤ allowance) (hN : N ≤ b) :
    ∀ (n pc : Nat) (s : S) (c : Nat) (ce : CertT), cert[pc]? = some ce → ce.live = true →
      Left ce.x ce.y ce.paused b c → Post N M P b (runT code n pc s c) := by
  intro n
  induction n with
  | zero =>
    intro pc s c ce hce hlive hl
    have hpc : pc < cert.length := (List.getElem?_eq_some_iff.mp hce).1
    have hs := hc pc hpc
    simp only [stepT, hce, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    obtain ⟨⟨hx, hy⟩, -⟩ := hs
    simp only [runT, S.failT, Post]
    exact left_mono hl (by omega) (by omega) (by simp)
  | succ n ih =>
    intro pc s c ce hce hlive hl
    have next : ∀ (q X Y : Nat) (p : Bool) (s' : S) (c' : Nat), covers cert q X Y p = true →
        Left X Y p b c' → Post N M P b (runT code n q s' c') := by
      intro q X Y p s' c' hcov hl'
      obtain ⟨ce', hce', hlive', hx', hy', hp'⟩ := covers_spec hcov
      exact ih q s' c' ce' hce' hlive' (left_mono hl' hx' hy' hp')
    have hpc : pc < cert.length := (List.getElem?_eq_some_iff.mp hce).1
    have hs := hc pc hpc
    simp only [stepT, hce, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    obtain ⟨⟨hx, hy⟩, hi⟩ := hs
    have hpos : 1 ≤ c := left_ge hl (by omega) (by omega)
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hl1 := left_tick hl
    have hfail : ∀ e, Post N M P b (s.failT e c) := by
      intro e
      simp only [S.failT, Post]
      exact left_mono hl1 hx hy (by simp)
    cases hcode : code[pc]? with
    | none => simp only [runT, hcode]; exact hfail _
    | some ins =>
      simp only [stepIns, hcode] at hi
      cases ins with
      | exit =>
        simp only [runT, hcode]
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at hi
        simp only [Post]
        refine left_mono hl1 hx hy (fun hP => ?_)
        rcases hi with hi | hi
        · rw [hi] at hP; contradiction
        · exact hi
      | lit v =>
        simp only [runT, hcode]
        exact next _ _ _ _ _ _ hi hl1
      | branch t =>
        simp only [runT, hcode]
        exact next _ _ _ _ _ _ hi hl1
      | zbranch t =>
        simp only [runT, hcode]
        simp only [Bool.and_eq_true] at hi
        split
        · split
          · exact next _ _ _ _ _ _ hi.1 hl1
          · exact next _ _ _ _ _ _ hi.2 hl1
        · exact hfail _
      | qdo t =>
        simp only [runT, hcode]
        simp only [Bool.and_eq_true] at hi
        split
        · split
          · exact next _ _ _ _ _ _ hi.1 hl1
          · exact next _ _ _ _ _ _ hi.2 hl1
        · exact hfail _
      | loop t =>
        simp only [runT, hcode]
        simp only [Bool.and_eq_true] at hi
        split
        · split
          · exact next _ _ _ _ _ _ hi.2 hl1
          · exact next _ _ _ _ _ _ hi.1 hl1
        · exact hfail _
      | ploop t =>
        simp only [runT, hcode]
        simp only [Bool.and_eq_true] at hi
        split
        · split
          · exact next _ _ _ _ _ _ hi.2 hl1
          · exact next _ _ _ _ _ _ hi.1 hl1
        · exact hfail _
        · exact hfail _
      | call f =>
        simp only [runT, hcode]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
        obtain ⟨⟨⟨⟨hxn, hyn⟩, hmn⟩, hmm⟩, hcov⟩ := hi
        have hf := callsCost hcalls hcode hce (by omega) s c (hl1.1)
          (left_ge hl1 (by omega) (by omega))
        split
        · rename_i s' c' heq
          rw [heq] at hf
          simp only [Post] at hf
          cases hp : ce.p
          · simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hcov
            rw [hp] at hf
            obtain ⟨ce1, h1, hlive1, hx1, hy1, hp1⟩ := covers_spec hcov.1
            obtain ⟨ce2, h2, _, hx2, hy2, _⟩ := covers_spec hcov.2
            have : ce1 = ce2 := by rw [h1] at h2; exact Option.some.inj h2
            subst this
            exact ih _ s' c' ce1 h1 hlive1
              (left_mono (left_call hb hl1 hf hx1 hy1 hx2 hy2) (Nat.le_refl _) (Nat.le_refl _) hp1)
          · simp only [hp, ↓reduceIte] at hcov
            rw [hp] at hf
            exact next _ _ _ _ _ _ hcov (left_paused hf)
        · rename_i fl c' heq
          rw [heq] at hf
          simp only [Post] at hf ⊢
          exact left_weaken (left_call hb hl1 (left_weaken hf) hxn hyn hmn hmm)
        · rename_i heq
          rw [heq] at hf
          exact hf.elim

theorem checkT_parts {code : List InsT} {cert : List CertT} {N M : Nat} {P : Bool}
    (h : checkT code cert N M P = true) :
    covers cert 0 0 0 false = true ∧ ∀ pc, pc < cert.length → stepT code cert N M P pc = true := by
  simp only [checkT, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h

/-- The bridge: a checked certificate, and callees that meet their Costs,
give the word its Cost. -/
theorem threadT_cost {code : List InsT} {cert : List CertT} {N M : Nat} {P : Bool}
    (hchk : checkT code cert N M P = true) (hcalls : CallsCost code cert) :
    Cost (threadT code) N M P := by
  obtain ⟨h0, hall⟩ := checkT_parts hchk
  obtain ⟨c0, hc0, hl0, hx0, hy0, hp0⟩ := covers_spec h0
  intro hM s b hb hN
  have hstart : Left c0.x c0.y c0.paused b b :=
    left_mono (show Left 0 0 false b b by simp [Left]; omega) hx0 hy0 hp0
  unfold threadT
  split
  · exact runT_sound hall hcalls hM hb hN _ 0 s b c0 hc0 hl0 hstart
  · simp [S.failT, Post, Left] <;> omega

/-- A task that starts f with its whole allowance, if the allowance covers
f's Cost, is never stopped by the watchdog while it runs f. -/
theorem Cost.never_stopped {f : SemT} {n m : Nat} {p : Bool} (h : Cost f n m p)
    (hn : n ≤ allowance) (hm : m ≤ allowance) (s : S) : f s allowance ≠ .watchdog := by
  intro heq
  have := h hm s allowance (Nat.le_refl _) hn
  rw [heq] at this
  exact this

end OS4

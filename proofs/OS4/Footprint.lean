import OS4.Machine

/-!
# Footprints, compositionally

`Foot f k j rk rj regs dout rout`: f, given k data items and rk return-stack
items, changes no memory outside the regions `regs` (bytes from a base, for a
length), and if it returns, leaves j and rj items whose values are as `dout`
and `rout` say. Regions and values are symbolic (`Val`): an input plus an
offset, the user area plus an offset, a word's address, a number, or unknown.

The footprint is the task's own writes. PAUSE lets other tasks and devices
change memory, so the statement is about addresses the outside world leaves
alone (`Quiet`); as `worldMem` is unknown, that is every address in a world
where no one else writes it.

A colon word's Foot comes from a certificate, as its Spec does: the symbolic
stacks before each instruction, found by tools/forth2lean.py. Lean checks it
(`fcheck`, by `decide`): each instruction takes its stacks to (something
weaker than) its successors', and each callee's regions, put in the caller's
terms, are among the caller's. `thread_foot` and `loopThread_foot` are the
bridges.
-/

namespace OS4

/-- What a symbolic value is relative to: a word's inputs and user area. -/
structure Env where
  ds : List Cell
  rs : List Cell
  up : Cell

/-- A cell as a word knows it at entry. `sum` appears only in primitives' outputs. -/
inductive Val where
  | any                         -- unknown
  | arg (i : Nat) (k : Cell)    -- data input i (0 the top) plus k
  | rarg (i : Nat) (k : Cell)   -- return-stack input i plus k
  | user (k : Cell)             -- the user area plus k
  | word (n : String) (k : Cell) -- a word's address plus k
  | kaddr (n : String) (k : Cell) -- a kernel variable's address plus k
  | top (k : Cell)              -- the dictionary's top less k
  | num (c : Cell)
  | sum (a b : Val)
deriving DecidableEq

def Val.eval (ρ : Env) : Val → Option Cell
  | any => none
  | arg i k => (ρ.ds[i]?).map (· + k)
  | rarg i k => (ρ.rs[i]?).map (· + k)
  | user k => some (ρ.up + k)
  | word n k => some (wordAddr n + k)
  | kaddr n k => some (kernelAddr n + k)
  | top k => some (dictTop - k)
  | num c => some c
  | sum a b => match a.eval ρ, b.eval ρ with
    | some x, some y => some (x + y)
    | _, _ => none

/-- x is the value v describes (anything, if v is unknown). -/
def Val.holds (v : Val) (ρ : Env) (x : Cell) : Prop := ∀ c, v.eval ρ = some c → x = c

def Val.shift (c : Cell) : Val → Val
  | any => any
  | arg i k => arg i (k + c)
  | rarg i k => rarg i (k + c)
  | user k => user (k + c)
  | word n k => word n (k + c)
  | kaddr n k => kaddr n (k + c)
  | top k => top (k - c)
  | num d => num (d + c)
  | sum _ _ => any

def Val.asNum : Val → Option Cell
  | num c => some c
  | _ => none

def Val.add (A B : Val) : Val :=
  match A.asNum, B.asNum with
  | some a, _ => B.shift a
  | none, some b => A.shift b
  | none, none => any

/-- A callee's value in its caller's terms, given the caller's symbolic
values of the callee's inputs. -/
def Val.subst (DS RS : List Val) : Val → Val
  | any => any
  | arg i k => (DS[i]?.getD any).shift k
  | rarg i k => (RS[i]?.getD any).shift k
  | user k => user k
  | word n k => word n k
  | kaddr n k => kaddr n k
  | top k => top k
  | num c => num c
  | sum a b => (a.subst DS RS).add (b.subst DS RS)

/-- Bytes from base, for len. Unknown base or length: anywhere. -/
structure Reg where
  base : Val
  len : Val
deriving DecidableEq

def Reg.has (r : Reg) (ρ : Env) (a : Cell) : Prop :=
  ∀ b l, r.base.eval ρ = some b → r.len.eval ρ = some l → (a - b).toNat < l.toNat

def Reg.subst (DS RS : List Val) (r : Reg) : Reg := ⟨r.base.subst DS RS, r.len.subst DS RS⟩

/-- Anywhere. -/
def Reg.all : Reg := ⟨.any, .any⟩

def Writes (regs : List Reg) (ρ : Env) (a : Cell) : Prop := ∃ r ∈ regs, r.has ρ a

/-- Nothing outside the task changes address a. -/
def Quiet (a : Cell) : Prop := ∀ n m, Prim.worldMem n m a = m a

/-- m keeps m0's bytes outside the regions (where the world is quiet). -/
def Kept (regs : List Reg) (ρ : Env) (m0 m : Mem) : Prop :=
  ∀ a, Quiet a → ¬ Writes regs ρ a → m a = m0 a

def resMem : Except Fail S → Mem
  | .ok s => s.mem
  | .error f => f.mem

/-- Each value describes the item at its index (items beyond are free). -/
def Agree (ρ : Env) (vs : List Val) (xs : List Cell) : Prop :=
  ∀ (i : Nat) (v : Val) (x : Cell), vs[i]? = some v → xs[i]? = some x → v.holds ρ x

def FOut (s r : List Cell) (u : Cell) (j rj : Nat) (ρ : Env) (dout rout : List Val) : Except Fail S → Prop
  | .ok st => st.ds.length = j + s.length ∧ st.ds.drop j = s ∧ Agree ρ dout st.ds ∧
              st.rs.length = rj + r.length ∧ st.rs.drop rj = r ∧ Agree ρ rout st.rs ∧ st.up = u
  | .error _ => True

def Foot (f : Sem) (k j rk rj : Nat) (regs : List Reg) (dout rout : List Val) : Prop :=
  ∀ (xs zs s r : List Cell) (m : Mem) (u : Cell) (e : Nat), xs.length = k → zs.length = rk →
    Kept regs ⟨xs, zs, u⟩ m (resMem (f ⟨xs ++ s, zs ++ r, m, u, e⟩)) ∧
    FOut s r u j rj ⟨xs, zs, u⟩ dout rout (f ⟨xs ++ s, zs ++ r, m, u, e⟩)

/-! ## Values -/

theorem holds_any (ρ : Env) (x : Cell) : Val.any.holds ρ x := by
  intro c h; simp [Val.eval] at h

theorem holds_num (c : Cell) (ρ : Env) : (Val.num c).holds ρ c := by
  intro d h; simp [Val.eval] at h; exact h
theorem holds_word (n : String) (k : Cell) (ρ : Env) : (Val.word n k).holds ρ (wordAddr n + k) := by
  intro d h; simp [Val.eval] at h; exact h
theorem holds_word0 (n : String) (ρ : Env) : (Val.word n 0).holds ρ (wordAddr n) := by
  intro d h; simp [Val.eval] at h; exact h
theorem holds_kaddr0 (n : String) (ρ : Env) : (Val.kaddr n 0).holds ρ (kernelAddr n) := by
  intro d h; simp [Val.eval] at h; exact h
theorem holds_top (k : Cell) (ρ : Env) : (Val.top k).holds ρ (dictTop - k) := by
  intro d h; simp [Val.eval] at h; exact h
theorem holds_top0 (ρ : Env) : (Val.top 0).holds ρ dictTop := by
  intro d h; simp [Val.eval] at h; exact h

theorem eval_shift {ρ : Env} {c x : Cell} :
    ∀ v : Val, (v.shift c).eval ρ = some x → ∃ y, v.eval ρ = some y ∧ x = y + c := by
  intro v h
  cases v with
  | any => simp [Val.shift, Val.eval] at h
  | sum a b => simp [Val.shift, Val.eval] at h
  | arg i k =>
    simp only [Val.shift, Val.eval] at h
    cases hz : ρ.ds[i]? with
    | none => simp [hz] at h
    | some z =>
      have hx : x = z + (k + c) := by simp [hz] at h; first | exact h.symm | exact h
      exact ⟨z + k, by simp [Val.eval, hz], by rw [hx, BitVec.add_assoc]⟩
  | rarg i k =>
    simp only [Val.shift, Val.eval] at h
    cases hz : ρ.rs[i]? with
    | none => simp [hz] at h
    | some z =>
      have hx : x = z + (k + c) := by simp [hz] at h; first | exact h.symm | exact h
      exact ⟨z + k, by simp [Val.eval, hz], by rw [hx, BitVec.add_assoc]⟩
  | user k =>
    simp only [Val.shift, Val.eval, Option.some.injEq] at h ⊢
    exact ⟨_, rfl, by rw [← h, BitVec.add_assoc]⟩
  | word n k =>
    simp only [Val.shift, Val.eval, Option.some.injEq] at h ⊢
    exact ⟨_, rfl, by rw [← h, BitVec.add_assoc]⟩
  | kaddr n k =>
    simp only [Val.shift, Val.eval, Option.some.injEq] at h ⊢
    exact ⟨_, rfl, by rw [← h, BitVec.add_assoc]⟩
  | top k =>
    simp only [Val.shift, Val.eval, Option.some.injEq] at h ⊢
    exact ⟨_, rfl, by rw [← h]; bv_omega⟩
  | num d =>
    simp only [Val.shift, Val.eval, Option.some.injEq] at h ⊢
    exact ⟨_, rfl, h.symm⟩

theorem eval_add {ρ : Env} {A B : Val} {c : Cell} (h : (A.add B).eval ρ = some c) :
    ∃ a b, A.eval ρ = some a ∧ B.eval ρ = some b ∧ c = a + b := by
  have num : ∀ {V : Val} {a : Cell}, V.asNum = some a → V.eval ρ = some a := by
    intro V a h
    cases V <;> simp [Val.asNum] at h
    simp [Val.eval, h]
  unfold Val.add at h
  cases ha : A.asNum with
  | some a =>
    simp only [ha] at h
    obtain ⟨y, hy, rfl⟩ := eval_shift B h
    exact ⟨a, y, num ha, hy, BitVec.add_comm _ _⟩
  | none =>
    cases hb : B.asNum with
    | some b =>
      simp only [ha, hb] at h
      obtain ⟨y, hy, rfl⟩ := eval_shift A h
      exact ⟨y, b, hy, num hb, rfl⟩
    | none => simp [ha, hb, Val.eval] at h

/-! ## Agreement -/

theorem agree_nil (ρ : Env) (xs : List Cell) : Agree ρ [] xs := by
  intro i v x h; simp at h

theorem agree_cons {ρ : Env} {v : Val} {vs : List Val} {x : Cell} {xs : List Cell} :
    Agree ρ (v :: vs) (x :: xs) ↔ v.holds ρ x ∧ Agree ρ vs xs := by
  constructor
  · intro h
    exact ⟨h 0 v x rfl rfl, fun i w y h1 h2 => h (i + 1) w y h1 h2⟩
  · rintro ⟨h0, h⟩ i w y h1 h2
    cases i with
    | zero => simp at h1 h2; subst h1 h2; exact h0
    | succ i => exact h i w y h1 h2

theorem agree_cons_nil {ρ : Env} {v : Val} {vs : List Val} : Agree ρ (v :: vs) [] := by
  intro i w y _ h2; simp at h2

theorem agree_tail {ρ : Env} {v : Val} {vs : List Val} {x : Cell} {xs : List Cell}
    (h : Agree ρ (v :: vs) (x :: xs)) : Agree ρ vs xs := (agree_cons.mp h).2

theorem agree_append {ρ : Env} {A B : List Val} {X Y : List Cell} (hl : A.length = X.length)
    (ha : Agree ρ A X) (hb : Agree ρ B Y) : Agree ρ (A ++ B) (X ++ Y) := by
  intro i v x h1 h2
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [List.getElem?_append_left hi] at h1
    rw [List.getElem?_append_left (by omega)] at h2
    exact ha i v x h1 h2
  · rw [List.getElem?_append_right hi] at h1
    rw [List.getElem?_append_right (by omega)] at h2
    rw [hl] at h1
    exact hb _ v x h1 h2

theorem agree_drop {ρ : Env} {A : List Val} {X : List Cell} (n : Nat) (h : Agree ρ A X) :
    Agree ρ (A.drop n) (X.drop n) := by
  intro i v x h1 h2
  rw [List.getElem?_drop] at h1 h2
  exact h _ v x h1 h2

theorem agree_take {ρ : Env} {A : List Val} {X : List Cell} (n : Nat) (h : Agree ρ A X) :
    Agree ρ (A.take n) (X.take n) := by
  intro i v x h1 h2
  rw [List.getElem?_take] at h1 h2
  by_cases hi : i < n
  · rw [if_pos hi] at h1 h2; exact h i v x h1 h2
  · rw [if_neg hi] at h1; simp at h1

/-- Agreement with a list whose items are all unknown, or `any`. -/
theorem agree_get {ρ : Env} {DS : List Val} {ys : List Cell} (hd : Agree ρ DS ys)
    (hl : DS.length = ys.length) {i : Nat} {w : Val} (h : DS[i]? = some w) :
    ∃ x, ys[i]? = some x ∧ w.holds ρ x := by
  have hi : i < ys.length := by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.mp h).1
  exact ⟨ys[i], List.getElem?_eq_getElem hi, hd i w _ h (List.getElem?_eq_getElem hi)⟩

/-- The heart of composition: a callee's value, put in its caller's terms,
evaluates (if at all) to what it did in the callee's. -/
theorem eval_subst {ρ : Env} {DS RS : List Val} {ys zs : List Cell}
    (hd : Agree ρ DS ys) (hdl : DS.length = ys.length) (hr : Agree ρ RS zs) (hrl : RS.length = zs.length) :
    ∀ (v : Val) {c : Cell}, (v.subst DS RS).eval ρ = some c → v.eval ⟨ys, zs, ρ.up⟩ = some c := by
  intro v
  induction v with
  | any => intro c h; simp [Val.subst, Val.eval] at h
  | arg i k =>
    intro c h
    simp only [Val.subst] at h
    obtain ⟨y, hy, rfl⟩ := eval_shift _ h
    cases hw : DS[i]? with
    | none => simp [hw, Val.eval] at hy
    | some w =>
      rw [hw, Option.getD_some] at hy
      obtain ⟨x, hx, hh⟩ := agree_get hd hdl hw
      simp [Val.eval, hx, hh y hy]
  | rarg i k =>
    intro c h
    simp only [Val.subst] at h
    obtain ⟨y, hy, rfl⟩ := eval_shift _ h
    cases hw : RS[i]? with
    | none => simp [hw, Val.eval] at hy
    | some w =>
      rw [hw, Option.getD_some] at hy
      obtain ⟨x, hx, hh⟩ := agree_get hr hrl hw
      simp [Val.eval, hx, hh y hy]
  | user k => intro c h; simpa [Val.subst, Val.eval] using h
  | word n k => intro c h; simpa [Val.subst, Val.eval] using h
  | kaddr n k => intro c h; simpa [Val.subst, Val.eval] using h
  | top k => intro c h; simpa [Val.subst, Val.eval] using h
  | num d => intro c h; simpa [Val.subst, Val.eval] using h
  | sum a b iha ihb =>
    intro c h
    simp only [Val.subst] at h
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add h
    simp [Val.eval, iha hx, ihb hy]

theorem holds_subst {ρ : Env} {DS RS : List Val} {ys zs : List Cell}
    (hd : Agree ρ DS ys) (hdl : DS.length = ys.length) (hr : Agree ρ RS zs) (hrl : RS.length = zs.length)
    {v : Val} {x : Cell} (h : v.holds ⟨ys, zs, ρ.up⟩ x) : (v.subst DS RS).holds ρ x :=
  fun c hc => h c (eval_subst hd hdl hr hrl v hc)

theorem agree_subst {ρ : Env} {DS RS : List Val} {ys zs : List Cell}
    (hd : Agree ρ DS ys) (hdl : DS.length = ys.length) (hr : Agree ρ RS zs) (hrl : RS.length = zs.length)
    {vs : List Val} {xs : List Cell} (h : Agree ⟨ys, zs, ρ.up⟩ vs xs) :
    Agree ρ (vs.map (Val.subst DS RS)) xs := by
  intro i v x h1 h2
  rw [List.getElem?_map] at h1
  cases hv : vs[i]? with
  | none => simp [hv] at h1
  | some w =>
    simp [hv] at h1
    subst h1
    exact holds_subst hd hdl hr hrl (h i w x hv h2)

theorem has_subst {ρ : Env} {DS RS : List Val} {ys zs : List Cell}
    (hd : Agree ρ DS ys) (hdl : DS.length = ys.length) (hr : Agree ρ RS zs) (hrl : RS.length = zs.length)
    {r : Reg} {a : Cell} (h : r.has ⟨ys, zs, ρ.up⟩ a) : (r.subst DS RS).has ρ a :=
  fun b l hb hl => h b l (eval_subst hd hdl hr hrl _ hb) (eval_subst hd hdl hr hrl _ hl)

/-! ## Certificates -/

/-- v is at least as precise as w. -/
def leV (v w : Val) : Bool := decide (w = .any) || decide (v = w)

def leL : List Val → List Val → Bool
  | [], [] => true
  | v :: vs, w :: ws => leV v w && leL vs ws
  | _, _ => false

theorem leL_length : ∀ {vs ws : List Val}, leL vs ws = true → vs.length = ws.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [leL, Bool.and_eq_true] at h
    simp [leL_length h.2]
  | [], _ :: _, h => by simp [leL] at h
  | _ :: _, [], h => by simp [leL] at h

theorem leL_agree {ρ : Env} : ∀ {vs ws : List Val} {xs : List Cell}, leL vs ws = true →
    Agree ρ vs xs → Agree ρ ws xs
  | [], [], _, _, h => h
  | v :: vs, w :: ws, xs, hl, h => by
    simp only [leL, leV, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hl
    cases xs with
    | nil => exact agree_cons_nil
    | cons x xs =>
      rw [agree_cons] at h ⊢
      refine ⟨?_, leL_agree hl.2 h.2⟩
      rcases hl.1 with hw | hw
      · subst hw; exact holds_any ρ x
      · subst hw; exact h.1
  | [], _ :: _, _, hl, _ => by simp [leL] at hl
  | _ :: _, [], _, hl, _ => by simp [leL] at hl

/-- The symbolic stacks before one instruction; for a call, the callee's
summary; for a literal, its value. Unreachable instructions are dead. -/
structure FCert where
  live : Bool
  ds : List Val
  rs : List Val
  k : Nat
  j : Nat
  rk : Nat
  rj : Nat
  regs : List Reg
  dout : List Val
  rout : List Val
  lv : Val

/-- Instruction p is live, and its stacks are no more precise than these. -/
def atF (cert : List FCert) (p : Nat) (ds rs : List Val) : Bool :=
  match cert[p]? with
  | some c => c.live && leL ds c.ds && leL rs c.rs
  | none => false

/-- A region the word's own regions include. -/
def coveredBy (regs : List Reg) (r : Reg) : Bool := decide (r ∈ regs) || decide (Reg.all ∈ regs)

def fstep (code : List Ins) (cert : List FCert) (regs : List Reg) (dout : List Val) (pc : Nat) : Bool :=
  match cert[pc]? with
  | none => false
  | some c =>
    !c.live ||
    match code[pc]? with
    | none => true
    | some (.call _) =>
      let DS := c.ds.take c.k
      let RS := c.rs.take c.rk
      decide (c.k ≤ c.ds.length) && decide (c.rk ≤ c.rs.length) &&
      decide (c.dout.length = c.j) && decide (c.rout.length = c.rj) &&
      c.regs.all (fun r => coveredBy regs (r.subst DS RS)) &&
      atF cert (pc + 1) (c.dout.map (Val.subst DS RS) ++ c.ds.drop c.k)
        (c.rout.map (Val.subst DS RS) ++ c.rs.drop c.rk)
    | some (.lit _) => atF cert (pc + 1) (c.lv :: c.ds) c.rs
    | some (.branch t) => atF cert t c.ds c.rs
    | some (.zbranch t) =>
      match c.ds with
      | _ :: ds => atF cert t ds c.rs && atF cert (pc + 1) ds c.rs
      | [] => false
    | some (.qdo t) =>
      match c.ds with
      | st :: li :: ds => atF cert t ds c.rs && atF cert (pc + 1) ds (st :: li :: c.rs)
      | _ => false
    | some (.loop t) =>
      match c.rs with
      | _ :: l :: rs => atF cert t c.ds (.any :: l :: rs) && atF cert (pc + 1) c.ds rs
      | _ => false
    | some (.ploop t) =>
      match c.ds, c.rs with
      | _ :: ds, _ :: l :: rs => atF cert t ds (.any :: l :: rs) && atF cert (pc + 1) ds rs
      | _, _ => false
    | some .exit => leL c.ds dout && decide (c.rs = [])

/-- The word's inputs, as it sees them at entry. -/
def argList (n : Nat) : List Val := (List.range n).map fun i => .arg i 0

/-- The certificate for a word taking inp items, writing in regs, leaving out items as dout. -/
def fcheck (code : List Ins) (cert : List FCert) (inp out : Nat) (regs : List Reg) (dout : List Val) : Bool :=
  decide (dout.length = out) && atF cert 0 (argList inp) [] &&
    (List.range code.length).all (fstep code cert regs dout)

/-- Each call meets the Foot its certificate entry claims; each literal is its value. -/
def InsFoot : Ins → FCert → Prop
  | .call f, c => Foot f c.k c.j c.rk c.rj c.regs c.dout c.rout
  | .lit v, c => ∀ ρ, c.lv.holds ρ v
  | _, _ => True

def InsFoots : List Ins → List FCert → Prop
  | [], _ => True
  | _ :: _, [] => True
  | i :: is, c :: cs => InsFoot i c ∧ InsFoots is cs

theorem insFoots {code : List Ins} {cert : List FCert} (h : InsFoots code cert) :
    ∀ {pc : Nat} {i : Ins} {c : FCert}, code[pc]? = some i → cert[pc]? = some c → InsFoot i c := by
  induction code generalizing cert with
  | nil => intro pc i c h1; simp at h1
  | cons i is ih =>
    cases cert with
    | nil => intro pc i c _ h2; simp at h2
    | cons c' cs =>
      obtain ⟨hi, hrest⟩ := h
      intro pc i c h1 h2
      cases pc with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        exact hi
      | succ pc =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih hrest h1 h2

theorem atF_spec {cert : List FCert} {p : Nat} {ds rs : List Val} (h : atF cert p ds rs = true) :
    ∃ c, cert[p]? = some c ∧ c.live = true ∧ leL ds c.ds = true ∧ leL rs c.rs = true := by
  unfold atF at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true] at h
    exact ⟨c, hc, h.1.1, h.1.2, h.2⟩
  · contradiction

theorem coveredBy_writes {regs : List Reg} {r : Reg} {ρ : Env} {a : Cell}
    (hc : coveredBy regs r = true) (h : r.has ρ a) : Writes regs ρ a := by
  simp only [coveredBy, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with hm | hm
  · exact ⟨r, hm, h⟩
  · exact ⟨Reg.all, hm, fun b l hb _ => by simp [Reg.all, Val.eval] at hb⟩

theorem kept_fail {regs : List Reg} {ρ : Env} {m0 : Mem} (s : S) (err : Err)
    (h : Kept regs ρ m0 s.mem) : Kept regs ρ m0 (resMem (s.fail err : Except Fail S)) := h

/-! ## The bridge -/

/-- What a run from some instruction must end with. -/
def FRes (regs : List Reg) (dout : List Val) (ρ : Env) (m0 : Mem) (s r : List Cell) (u : Cell) (out : Nat)
    (res : Except Fail S) : Prop :=
  Kept regs ρ m0 (resMem res) ∧ FOut s r u out 0 ρ dout [] res

theorem run_foot {code : List Ins} {cert : List FCert} {regs : List Reg} {dout : List Val} {out : Nat}
    {xs0 s r : List Cell} {u : Cell} {m0 : Mem} (hout : dout.length = out)
    (hc : ∀ pc, pc < code.length → fstep code cert regs dout pc = true) (hins : InsFoots code cert) :
    ∀ (n pc : Nat) (ys zs : List Cell) (m : Mem) (e : Nat) (c : FCert),
      cert[pc]? = some c → c.live = true → ys.length = c.ds.length → zs.length = c.rs.length →
      Agree ⟨xs0, [], u⟩ c.ds ys → Agree ⟨xs0, [], u⟩ c.rs zs → Kept regs ⟨xs0, [], u⟩ m0 m →
      FRes regs dout ⟨xs0, [], u⟩ m0 s r u out (run code n pc ⟨ys ++ s, zs ++ r, m, u, e⟩) := by
  intro n
  induction n with
  | zero => intro pc ys zs m e c _ _ _ _ _ _ hk; exact ⟨hk, trivial⟩
  | succ n ih =>
    intro pc ys zs m e c hcpc hlive hys hzs hay haz hk
    have next : ∀ {p : Nat} {ds' rs' : List Val} (ys' zs' : List Cell) (m' : Mem) (e' : Nat),
        atF cert p ds' rs' = true → ys'.length = ds'.length → zs'.length = rs'.length →
        Agree ⟨xs0, [], u⟩ ds' ys' → Agree ⟨xs0, [], u⟩ rs' zs' → Kept regs ⟨xs0, [], u⟩ m0 m' →
        FRes regs dout ⟨xs0, [], u⟩ m0 s r u out (run code n p ⟨ys' ++ s, zs' ++ r, m', u, e'⟩) := by
      intro p ds' rs' ys' zs' m' e' h h1 h2 h3 h4 h5
      obtain ⟨c', hc', hl', hd', hr'⟩ := atF_spec h
      exact ih p ys' zs' m' e' c' hc' hl' (by rw [h1, leL_length hd']) (by rw [h2, leL_length hr'])
        (leL_agree hd' h3) (leL_agree hr' h4) h5
    have failed : ∀ err, FRes regs dout ⟨xs0, [], u⟩ m0 s r u out
        ((⟨ys ++ s, zs ++ r, m, u, e⟩ : S).fail err) := fun err => ⟨hk, trivial⟩
    cases hcode : code[pc]? with
    | none => simp only [run, hcode]; exact failed _
    | some ins =>
      have hpc : pc < code.length := by
        rcases Nat.lt_or_ge pc code.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hcode
          contradiction
      have hs := hc pc hpc
      have hi := insFoots hins hcode hcpc
      simp only [fstep, hcpc, hlive, hcode, Bool.not_true, Bool.false_or] at hs
      cases ins with
      | exit =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨hd, hr⟩ := hs
        rw [hr] at hzs
        have hz : zs = [] := List.eq_nil_of_length_eq_zero hzs
        subst hz
        simp only [run, hcode]
        refine ⟨hk, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp [hys, leL_length hd, hout]
        · simp [hys, leL_length hd, hout]
        · intro i v x h1 h2
          rw [List.getElem?_append_left (by rw [hys, leL_length hd]; exact (List.getElem?_eq_some_iff.mp h1).1)] at h2
          exact leL_agree hd hay i v x h1 h2
        · simp
        · simp
        · exact agree_nil _ _
      | lit v =>
        simp only [run, hcode]
        exact next (v :: ys) zs m e hs (by simp [hys]) hzs (agree_cons.mpr ⟨hi _, hay⟩) haz hk
      | branch t =>
        simp only [run, hcode]
        exact next ys zs m e hs hys hzs hay haz hk
      | zbranch t =>
        cases hcd : c.ds with
        | nil => rw [hcd] at hs; simp at hs
        | cons w ds =>
          rw [hcd] at hs hys hay
          simp only [Bool.and_eq_true] at hs
          cases ys with
          | nil => simp at hys
          | cons x ys' =>
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hys
            have ht := agree_tail hay
            simp only [run, hcode, List.cons_append]
            split
            · exact next ys' zs m e hs.1 hys hzs ht haz hk
            · exact next ys' zs m e hs.2 hys hzs ht haz hk
      | qdo t =>
        rcases hcd : c.ds with _ | ⟨st, _ | ⟨li, ds⟩⟩ <;> rw [hcd] at hs hys hay <;> (try simp at hs)
        try simp only [Bool.and_eq_true] at hs
        rcases ys with _ | ⟨a, _ | ⟨b, ys'⟩⟩ <;> simp at hys
        have h1 := agree_cons.mp hay
        have h2 := agree_cons.mp h1.2
        simp only [run, hcode, List.cons_append]
        split
        · exact next ys' zs m e hs.1 hys hzs h2.2 haz hk
        · exact next ys' (a :: b :: zs) m e hs.2 hys (by simp [hzs])
            h2.2 (agree_cons.mpr ⟨h1.1, agree_cons.mpr ⟨h2.1, haz⟩⟩) hk
      | loop t =>
        rcases hcr : c.rs with _ | ⟨w, _ | ⟨l, rs⟩⟩ <;> rw [hcr] at hs hzs haz <;> (try simp at hs)
        try simp only [Bool.and_eq_true] at hs
        rcases zs with _ | ⟨i, _ | ⟨lv, zs'⟩⟩ <;> simp at hzs
        have h1 := agree_cons.mp haz
        have h2 := agree_cons.mp h1.2
        simp only [run, hcode, List.cons_append]
        split
        · exact next ys zs' m e hs.2 hys hzs hay h2.2 hk
        · exact next ys ((i + 1) :: lv :: zs') m e hs.1 hys (by simp [hzs])
            hay (agree_cons.mpr ⟨holds_any _ _, agree_cons.mpr ⟨h2.1, h2.2⟩⟩) hk
      | ploop t =>
        rcases hcd : c.ds with _ | ⟨w, ds⟩ <;> rw [hcd] at hs hys hay <;> (try simp at hs)
        rcases hcr : c.rs with _ | ⟨w', _ | ⟨l, rs⟩⟩ <;> rw [hcr] at hs hzs haz <;> (try simp at hs)
        try simp only [Bool.and_eq_true] at hs
        rcases ys with _ | ⟨k, ys'⟩ <;> simp at hys
        rcases zs with _ | ⟨i, _ | ⟨lv, zs'⟩⟩ <;> simp at hzs
        have ha := agree_tail hay
        have h1 := agree_cons.mp haz
        have h2 := agree_cons.mp h1.2
        simp only [run, hcode, List.cons_append]
        split
        · exact next ys' zs' m e hs.2 hys hzs ha h2.2 hk
        · exact next ys' ((i + k) :: lv :: zs') m e hs.1 hys (by simp [hzs])
            ha (agree_cons.mpr ⟨holds_any _ _, agree_cons.mpr ⟨h2.1, h2.2⟩⟩) hk
      | call f =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
        obtain ⟨⟨⟨⟨⟨hk1, hrk⟩, hdj⟩, hrj⟩, hcov⟩, hn⟩ := hs
        have hft := hi (ys.take c.k) (zs.take c.rk) (ys.drop c.k ++ s) (zs.drop c.rk ++ r) m u e
          (by simp; omega) (by simp; omega)
        have e1 : ys.take c.k ++ (ys.drop c.k ++ s) = ys ++ s := by
          rw [← List.append_assoc, List.take_append_drop]
        have e2 : zs.take c.rk ++ (zs.drop c.rk ++ r) = zs ++ r := by
          rw [← List.append_assoc, List.take_append_drop]
        rw [e1, e2] at hft
        obtain ⟨hkept, hfo⟩ := hft
        have hd := agree_take c.k hay
        have hr := agree_take c.rk haz
        have hdl : (c.ds.take c.k).length = (ys.take c.k).length := by simp [hys]
        have hrl : (c.rs.take c.rk).length = (zs.take c.rk).length := by simp [hzs]
        -- the callee's writes are among the word's
        have hk' : ∀ m', Kept c.regs ⟨ys.take c.k, zs.take c.rk, u⟩ m m' → Kept regs ⟨xs0, [], u⟩ m0 m' := by
          intro m' hm a hq hw
          rw [hm a hq ?_, hk a hq hw]
          rintro ⟨r', hr', hh⟩
          exact hw (coveredBy_writes (hcov r' hr') (has_subst (ρ := ⟨xs0, [], u⟩) hd hdl hr hrl hh))
        simp only [run, hcode]
        split
        · rename_i st' hst
          rw [hst] at hkept hfo
          obtain ⟨hl1, hd1, ha1, hl2, hd2, ha2, hup⟩ := hfo
          obtain ⟨ds', rs', m', u', e'⟩ := st'
          simp only at hl1 hd1 ha1 hl2 hd2 ha2 hup hkept
          subst u'
          have eds : ds' = ds'.take c.j ++ (ys.drop c.k ++ s) := by
            conv => lhs; rw [← List.take_append_drop c.j ds']
            rw [hd1]
          have ers : rs' = rs'.take c.rj ++ (zs.drop c.rk ++ r) := by
            conv => lhs; rw [← List.take_append_drop c.rj rs']
            rw [hd2]
          rw [eds, ers, ← List.append_assoc, ← List.append_assoc]
          have hlj : (ds'.take c.j).length = c.j := by simp; omega
          have hlrj : (rs'.take c.rj).length = c.rj := by simp; omega
          refine next _ _ m' e' hn ?_ ?_ ?_ ?_ (hk' m' hkept)
          · simp [hlj, hdj, hys]
          · simp [hlrj, hrj, hzs]
          · refine agree_append (by simp [hlj, hdj]) ?_ (agree_drop c.k hay)
            exact agree_subst (ρ := ⟨xs0, [], u⟩) hd hdl hr hrl (agree_take_of ha1)
          · refine agree_append (by simp [hlrj, hrj]) ?_ (agree_drop c.rk haz)
            exact agree_subst (ρ := ⟨xs0, [], u⟩) hd hdl hr hrl (agree_take_of ha2)
        · rename_i fl hst
          rw [hst] at hkept
          exact ⟨hk' _ hkept, trivial⟩
where
  agree_take_of {ρ : Env} {vs : List Val} {xs : List Cell} {n : Nat} (h : Agree ρ vs xs) :
      Agree ρ vs (xs.take n) := by
    intro i v x h1 h2
    rw [List.getElem?_take] at h2
    by_cases hi : i < n
    · rw [if_pos hi] at h2; exact h i v x h1 h2
    · rw [if_neg hi] at h2; simp at h2

theorem agree_args {ρ : Env} : Agree ρ (argList ρ.ds.length) ρ.ds := by
  intro i v x h1 h2
  have hi : i < ρ.ds.length := (List.getElem?_eq_some_iff.mp h2).1
  simp [argList, hi] at h1
  subst h1
  intro c hc
  simp [Val.eval, h2] at hc
  exact hc

theorem fcheck_parts {code : List Ins} {cert : List FCert} {inp out : Nat} {regs : List Reg} {dout : List Val}
    (h : fcheck code cert inp out regs dout = true) :
    dout.length = out ∧ atF cert 0 (argList inp) [] = true ∧
      ∀ pc, pc < code.length → fstep code cert regs dout pc = true := by
  simp only [fcheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem start_foot {code : List Ins} {cert : List FCert} {inp out : Nat} {regs : List Reg} {dout : List Val}
    (hchk : fcheck code cert inp out regs dout = true) (hins : InsFoots code cert) (n : Nat)
    (xs s r : List Cell) (m : Mem) (u : Cell) (e : Nat) (hx : xs.length = inp) :
    FRes regs dout ⟨xs, [], u⟩ m s r u out (run code n 0 ⟨xs ++ s, [] ++ r, m, u, e⟩) := by
  obtain ⟨hout, h0, hall⟩ := fcheck_parts hchk
  obtain ⟨c0, hc0, hl0, hd0, hr0⟩ := atF_spec h0
  have ha : Agree (⟨xs, [], u⟩ : Env) (argList inp) xs := by
    have := agree_args (ρ := ⟨xs, [], u⟩)
    simp only at this
    rw [hx] at this
    exact this
  exact run_foot hout hall hins n 0 xs [] m e c0 hc0 hl0
    (by rw [← leL_length hd0]; simp [argList, hx]) (by rw [← leL_length hr0]; rfl)
    (leL_agree hd0 ha) (leL_agree hr0 (agree_nil _ _)) (fun _ _ _ => rfl)

/-- The bridge, for a word without loops. -/
theorem thread_foot {code : List Ins} {cert : List FCert} {inp out : Nat} {regs : List Reg} {dout : List Val}
    (hchk : fcheck code cert inp out regs dout = true) (hins : InsFoots code cert) :
    Foot (thread code) inp out 0 0 regs dout [] := by
  intro xs zs s r m u e hx hz
  have hz' : zs = [] := List.eq_nil_of_length_eq_zero hz
  subst hz'
  exact start_foot hchk hins code.length xs s r m u e hx

/-- The bridge, for a word with loops. -/
theorem loopThread_foot {code : List Ins} {cert : List FCert} {inp out : Nat} {regs : List Reg} {dout : List Val}
    (hchk : fcheck code cert inp out regs dout = true) (hins : InsFoots code cert) :
    Foot (loopThread code) inp out 0 0 regs dout [] := by
  intro xs zs s r m u e hx hz
  have hz' : zs = [] := List.eq_nil_of_length_eq_zero hz
  subst hz'
  unfold loopThread
  split
  · exact start_foot hchk hins _ xs s r m u e hx
  · exact ⟨fun _ _ _ => rfl, trivial⟩

end OS4

import OS4.Machine

/-!
# Stack effects, compositionally

`Spec f k j rk rj`: f takes k data items and rk return-stack items and, if it
returns, leaves j and rj in their place. It touches nothing below them, and
leaves the user area alone. Errors are allowed: this is about shape, not about
success.

A colon word's Spec comes from a certificate: the depths of both stacks
before each instruction of its thread, found by tools/forth2lean.py. Lean
checks the certificate (`check`, by `decide`): each instruction takes its
depths to its successors'. The bridge theorems `thread_spec` and
`loopThread_spec` say that a checked certificate, and calls that meet their
callees' Specs, make the whole word meet its Spec. Each word is proven once,
from its callees' theorems, and no proof unfolds another word.
-/

namespace OS4

/-- What a word must leave: j items above s, rj above r, the user area u. -/
def Out (s r : List Cell) (u : Cell) (j rj : Nat) : Except Fail S → Prop
  | .ok st => (∃ ys, ys.length = j ∧ st.ds = ys ++ s) ∧ (∃ ws, ws.length = rj ∧ st.rs = ws ++ r) ∧ st.up = u
  | .error _ => True

def Spec (f : Sem) (k j rk rj : Nat) : Prop :=
  ∀ (xs zs s r : List Cell) (m : Mem) (u : Cell) (e : Nat), xs.length = k → zs.length = rk →
    Out s r u j rj (f ⟨xs ++ s, zs ++ r, m, u, e⟩)

theorem exists_prefix (l s : List Cell) (j : Nat) :
    (∃ ys : List Cell, ys.length = j ∧ l = ys ++ s) ↔ (l.length = j + s.length ∧ l.drop j = s) := by
  constructor
  · rintro ⟨ys, rfl, rfl⟩
    simp
  · rintro ⟨h1, h2⟩
    refine ⟨l.take j, by simp; omega, ?_⟩
    conv => lhs; rw [← List.take_append_drop j l]
    rw [h2]

/-! ## Certificates -/

/-- The depths before one instruction, counted above the word's own floor;
for a call, the Spec the callee meets. Unreachable instructions are dead. -/
structure Cert where
  live : Bool
  d : Nat
  r : Nat
  k : Nat
  j : Nat
  rk : Nat
  rj : Nat

/-- Instruction p is live, with these depths. -/
def at? (cert : List Cert) (p d r : Nat) : Bool :=
  match cert[p]? with
  | some c => c.live && c.d == d && c.r == r
  | none => false

/-- Instruction pc takes its depths to those of every successor. -/
def stepOK (code : List Ins) (cert : List Cert) (out pc : Nat) : Bool :=
  match cert[pc]? with
  | none => false
  | some c =>
    !c.live ||
    match code[pc]? with
    | none => true
    | some (.call _) =>
      decide (c.k ≤ c.d) && decide (c.rk ≤ c.r) && at? cert (pc + 1) (c.d - c.k + c.j) (c.r - c.rk + c.rj)
    | some (.lit _) => at? cert (pc + 1) (c.d + 1) c.r
    | some (.branch t) => at? cert t c.d c.r
    | some (.zbranch t) =>
      decide (1 ≤ c.d) && at? cert t (c.d - 1) c.r && at? cert (pc + 1) (c.d - 1) c.r
    | some (.qdo t) =>
      decide (2 ≤ c.d) && at? cert t (c.d - 2) c.r && at? cert (pc + 1) (c.d - 2) (c.r + 2)
    | some (.loop t) =>
      decide (2 ≤ c.r) && at? cert t c.d c.r && at? cert (pc + 1) c.d (c.r - 2)
    | some (.ploop t) =>
      decide (1 ≤ c.d) && decide (2 ≤ c.r) && at? cert t (c.d - 1) c.r && at? cert (pc + 1) (c.d - 1) (c.r - 2)
    | some .exit => c.d == out && c.r == 0

/-- The certificate for a word taking inp items and leaving out. -/
def check (code : List Ins) (cert : List Cert) (inp out : Nat) : Bool :=
  at? cert 0 inp 0 && (List.range code.length).all (stepOK code cert out)

/-- Each call meets the Spec its certificate entry claims. -/
def InsMeets : Ins → Cert → Prop
  | .call f, c => Spec f c.k c.j c.rk c.rj
  | _, _ => True

def CallsMeet : List Ins → List Cert → Prop
  | [], _ => True
  | _ :: _, [] => True
  | i :: is, c :: cs => InsMeets i c ∧ CallsMeet is cs

theorem at?_spec {cert : List Cert} {p d r : Nat} (h : at? cert p d r = true) :
    ∃ c, cert[p]? = some c ∧ c.live = true ∧ c.d = d ∧ c.r = r := by
  unfold at? at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, hc, h.1.1, h.1.2, h.2⟩
  · contradiction

theorem callsMeet {code : List Ins} {cert : List Cert} (h : CallsMeet code cert) :
    ∀ {pc : Nat} {f : Sem} {c : Cert}, code[pc]? = some (.call f) → cert[pc]? = some c →
      Spec f c.k c.j c.rk c.rj := by
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

/-! ## The bridge -/

/-- Running a checked thread from a live instruction, with the stacks as its
certificate says, ends as the word's Spec says (or fails). -/
theorem run_sound {code : List Ins} {cert : List Cert} {out : Nat} {s r : List Cell} {u : Cell}
    (hc : ∀ pc, pc < code.length → stepOK code cert out pc = true) (hcalls : CallsMeet code cert) :
    ∀ (n pc : Nat) (ys zs : List Cell) (m : Mem) (e : Nat) (c : Cert),
      cert[pc]? = some c → c.live = true → ys.length = c.d → zs.length = c.r →
      Out s r u out 0 (run code n pc ⟨ys ++ s, zs ++ r, m, u, e⟩) := by
  intro n
  induction n with
  | zero => intros; simp [run, S.fail, Out]
  | succ n ih =>
    intro pc ys zs m e c hcpc hlive hys hzs
    have next : ∀ {p d' r' : Nat} (ys' zs' : List Cell) (m' : Mem) (e' : Nat),
        at? cert p d' r' = true → ys'.length = d' → zs'.length = r' →
        Out s r u out 0 (run code n p ⟨ys' ++ s, zs' ++ r, m', u, e'⟩) := by
      intro p d' r' ys' zs' m' e' h h1 h2
      obtain ⟨c', hc', hl', hd', hr'⟩ := at?_spec h
      exact ih p ys' zs' m' e' c' hc' hl' (by omega) (by omega)
    cases hcode : code[pc]? with
    | none => simp [run, hcode, S.fail, Out]
    | some ins =>
      have hpc : pc < code.length := by
        rcases Nat.lt_or_ge pc code.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hcode
          contradiction
      have hs := hc pc hpc
      simp only [stepOK, hcpc, hlive, hcode, Bool.not_true, Bool.false_or] at hs
      cases ins with
      | exit =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨hd, hr⟩ := hs
        have hz : zs = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hz
        simp only [run, hcode, Out]
        exact ⟨⟨ys, by omega, rfl⟩, ⟨[], rfl, rfl⟩, trivial⟩
      | lit v =>
        simp only [run, hcode]
        exact next (v :: ys) zs m e hs (by simp; omega) hzs
      | branch t =>
        simp only [run, hcode]
        exact next ys zs m e hs hys hzs
      | zbranch t =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hd, ht⟩, hn⟩ := hs
        cases ys with
        | nil => simp at hys; omega
        | cons x ys' =>
          simp only [List.length_cons] at hys
          simp only [run, hcode, List.cons_append]
          split
          · exact next ys' zs m e ht (by omega) hzs
          · exact next ys' zs m e hn (by omega) hzs
      | qdo t =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hd, ht⟩, hn⟩ := hs
        match ys, hys with
        | [], hys => simp at hys; omega
        | [_], hys => simp at hys; omega
        | a :: b :: ys', hys =>
          simp only [List.length_cons] at hys
          simp only [run, hcode, List.cons_append]
          split
          · exact next ys' zs m e ht (by omega) hzs
          · exact next ys' (a :: b :: zs) m e hn (by omega) (by simp; omega)
      | loop t =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hr, ht⟩, hn⟩ := hs
        match zs, hzs with
        | [], hzs => simp at hzs; omega
        | [_], hzs => simp at hzs; omega
        | i :: l :: zs', hzs =>
          simp only [List.length_cons] at hzs
          simp only [run, hcode, List.cons_append]
          split
          · exact next ys zs' m e hn hys (by omega)
          · exact next ys ((i + 1) :: l :: zs') m e ht hys (by simp; omega)
      | ploop t =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨⟨hd, hr⟩, ht⟩, hn⟩ := hs
        match ys, hys, zs, hzs with
        | [], hys, _, _ => simp at hys; omega
        | _ :: _, _, [], hzs => simp at hzs; omega
        | _ :: _, _, [_], hzs => simp at hzs; omega
        | k :: ys', hys, i :: l :: zs', hzs =>
          simp only [List.length_cons] at hys hzs
          simp only [run, hcode, List.cons_append]
          split
          · exact next ys' zs' m e hn (by omega) (by omega)
          · exact next ys' ((i + k) :: l :: zs') m e ht (by omega) (by simp; omega)
      | call f =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hk, hrk⟩, hn⟩ := hs
        have hf := callsMeet hcalls hcode hcpc (ys.take c.k) (zs.take c.rk)
          (ys.drop c.k ++ s) (zs.drop c.rk ++ r) m u e (by simp; omega) (by simp; omega)
        have e1 : ys.take c.k ++ (ys.drop c.k ++ s) = ys ++ s := by
          rw [← List.append_assoc, List.take_append_drop]
        have e2 : zs.take c.rk ++ (zs.drop c.rk ++ r) = zs ++ r := by
          rw [← List.append_assoc, List.take_append_drop]
        rw [e1, e2] at hf
        simp only [run, hcode]
        split
        · rename_i st' hst
          rw [hst] at hf
          obtain ⟨⟨ys2, hl2, hds⟩, ⟨ws, hwl, hrs⟩, hup⟩ := hf
          obtain ⟨ds', rs', m', u', e'⟩ := st'
          simp only at hds hrs hup
          subst hds hrs hup
          have h := next (ys2 ++ ys.drop c.k) (ws ++ zs.drop c.rk) m' e' hn
            (by simp; omega) (by simp; omega)
          simpa only [List.append_assoc] using h
        · simp [Out]

theorem check_parts {code : List Ins} {cert : List Cert} {inp out : Nat}
    (h : check code cert inp out = true) :
    at? cert 0 inp 0 = true ∧ ∀ pc, pc < code.length → stepOK code cert out pc = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h

/-- The bridge, for a word without loops. -/
theorem thread_spec {code : List Ins} {cert : List Cert} {inp out : Nat}
    (hchk : check code cert inp out = true) (hcalls : CallsMeet code cert) :
    Spec (thread code) inp out 0 0 := by
  obtain ⟨h0, hall⟩ := check_parts hchk
  obtain ⟨c0, hc0, hl0, hd0, hr0⟩ := at?_spec h0
  intro xs zs s r m u e hx hz
  have hz' : zs = [] := List.eq_nil_of_length_eq_zero hz
  subst hz'
  exact run_sound hall hcalls code.length 0 xs [] m e c0 hc0 hl0 (by omega) (by simp; omega)

/-- The bridge, for a word with loops: whatever fuel it takes. -/
theorem loopThread_spec {code : List Ins} {cert : List Cert} {inp out : Nat}
    (hchk : check code cert inp out = true) (hcalls : CallsMeet code cert) :
    Spec (loopThread code) inp out 0 0 := by
  obtain ⟨h0, hall⟩ := check_parts hchk
  obtain ⟨c0, hc0, hl0, hd0, hr0⟩ := at?_spec h0
  intro xs zs s r m u e hx hz
  have hz' : zs = [] := List.eq_nil_of_length_eq_zero hz
  subst hz'
  unfold loopThread
  split
  · exact run_sound hall hcalls _ 0 xs [] m e c0 hc0 hl0 (by omega) (by simp; omega)
  · simp [S.fail, Out]

/-! ## Specs that follow from others -/

/-- Items below a word's inputs pass through it untouched. -/
theorem spec_frame {f : Sem} {k j rk rj : Nat} (h : Spec f k j rk rj) (n : Nat) :
    Spec f (k + n) (j + n) rk rj := by
  intro xs zs s r m u e hx hz
  have := h (xs.take k) zs (xs.drop k ++ s) r m u e (by simp; omega) hz
  rw [← List.append_assoc, List.take_append_drop] at this
  cases hres : f ⟨xs ++ s, zs ++ r, m, u, e⟩ with
  | error _ => simp [Out]
  | ok st =>
    rw [hres] at this
    simp only [Out] at this ⊢
    obtain ⟨⟨ys, hl, hds⟩, hrs, hup⟩ := this
    exact ⟨⟨ys ++ xs.drop k, by simp; omega, by simp [hds]⟩, hrs, hup⟩

theorem doesChild_spec {code : Sem} {k j rk rj : Nat} (b : Cell) (h : Spec code (k + 1) j rk rj) :
    Spec (doesChild b code) k j rk rj := by
  intro xs zs s r m u e hx hz
  exact h (b :: xs) zs s r m u e (by simp; omega) hz

theorem pushConst_spec (v : Cell) : Spec (pushConst v) 0 1 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ =>
    simp only [pushConst, Out]
    exact ⟨⟨[v], rfl, rfl⟩, ⟨[], rfl, rfl⟩, trivial⟩

theorem kconst_spec (name : String) : Spec (kconst name) 0 1 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ =>
    simp only [kconst, Out]
    exact ⟨⟨[_], rfl, rfl⟩, ⟨[], rfl, rfl⟩, trivial⟩

end OS4

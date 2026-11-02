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

/-- What `?dup` does: x stays, with a second copy unless it is zero, and
nothing else changes. Its depth afterwards depends on x, so a certificate
takes `?dup` together with the `0branch` that follows it (the `?dup if`
idiom): zero goes to the branch's target one item down, anything else on
with the depth it had. -/
def QDup (f : Sem) : Prop :=
  ∀ (x : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat),
    f ⟨x :: s, r, m, u, e⟩ = .ok ⟨if x = 0 then x :: s else x :: x :: s, r, m, u, e⟩

/-- What `0=` does, for the `?dup 0= if` idiom: zero still goes one item
down, but past the branch; anything else to the branch's target. -/
def ZEq (f : Sem) : Prop :=
  ∀ (x : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat),
    f ⟨x :: s, r, m, u, e⟩ = .ok ⟨(if x = 0 then -1 else 0) :: s, r, m, u, e⟩

/-- Push v, then run P and then L, as one step: `['] word sem locked`, where
v is the word's xt, P pushes the semaphore and L is LOCKED. -/
def seg3 (v : Cell) (P L : Sem) : Sem := fun s =>
  match P { s with ds := v :: s.ds } with
  | .ok s1 => L s1
  | .error e => .error e

/-! ## Certificates -/

/-- The depths before one instruction, counted above the word's own floor;
for a call, the Spec the callee meets, or q for a `?dup` before a
`0branch`, or before a `0=` and then a `0branch`, whose own entries are then
dead (the `0=`'s with z); for a literal with lk, the Spec of it and the two
calls after it as one step (`seg3`), whose own entries are then dead (with
lk). Unreachable instructions are dead. -/
structure Cert where
  live : Bool
  d : Nat
  r : Nat
  k : Nat
  j : Nat
  rk : Nat
  rj : Nat
  q : Bool
  z : Bool
  lk : Bool

/-- Instruction p's entry says it is `0=`. -/
def zAt (cert : List Cert) (p : Nat) : Bool :=
  match cert[p]? with
  | some c => c.z && !c.lk
  | none => false

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
      !c.lk && !c.z &&
      if c.q then
        decide (1 ≤ c.d) &&
        match code[pc + 1]?, code[pc + 2]? with
        | some (.zbranch t), _ => at? cert t (c.d - 1) c.r && at? cert (pc + 2) c.d c.r
        | some (.call _), some (.zbranch t) =>
          zAt cert (pc + 1) && at? cert (pc + 3) (c.d - 1) c.r && at? cert t c.d c.r
        | _, _ => false
      else
        decide (c.k ≤ c.d) && decide (c.rk ≤ c.r) && at? cert (pc + 1) (c.d - c.k + c.j) (c.r - c.rk + c.rj)
    | some (.lit _) =>
      if c.lk then
        match code[pc + 1]?, code[pc + 2]? with
        | some (.call _), some (.call _) =>
          decide (c.k ≤ c.d) && decide (c.rk ≤ c.r) && at? cert (pc + 3) (c.d - c.k + c.j) (c.r - c.rk + c.rj)
        | _, _ => false
      else at? cert (pc + 1) (c.d + 1) c.r
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

/-- Each call meets the Spec its certificate entry claims, or is `?dup` or
`0=`; a literal with lk, and the two calls after it, meet the Spec its entry
claims. An instruction sees the ones after it. -/
def InsMeets : Ins → List Ins → Cert → Prop
  | .call f, _, c => cond c.lk True (cond c.z (ZEq f) (cond c.q (QDup f) (Spec f c.k c.j c.rk c.rj)))
  | .lit v, .call P :: .call L :: _, c => cond c.lk (Spec (seg3 v P L) c.k c.j c.rk c.rj) True
  | _, _, _ => True

def CallsMeet : List Ins → List Cert → Prop
  | [], _ => True
  | _ :: _, [] => True
  | i :: is, c :: cs => InsMeets i is c ∧ CallsMeet is cs

theorem at?_spec {cert : List Cert} {p d r : Nat} (h : at? cert p d r = true) :
    ∃ c, cert[p]? = some c ∧ c.live = true ∧ c.d = d ∧ c.r = r := by
  unfold at? at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, hc, h.1.1, h.1.2, h.2⟩
  · contradiction

theorem callsMeet {code : List Ins} {cert : List Cert} (h : CallsMeet code cert) :
    ∀ {pc : Nat} {i : Ins} {c : Cert}, code[pc]? = some i → cert[pc]? = some c →
      InsMeets i (code.drop (pc + 1)) c := by
  induction code generalizing cert with
  | nil => intro pc i c h1; simp at h1
  | cons i0 is ih =>
    cases cert with
    | nil => intro pc i c _ h2; simp at h2
    | cons c' cs =>
      obtain ⟨hi, hrest⟩ := h
      intro pc i c h1 h2
      cases pc with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        simpa using hi
      | succ pc =>
        simp only [List.getElem?_cons_succ] at h1 h2
        simpa using ih hrest h1 h2

/-- The two instructions after pc, if they are there. -/
theorem drop_two {code : List Ins} {pc : Nat} {a b : Ins} (ha : code[pc + 1]? = some a)
    (hb : code[pc + 2]? = some b) : ∃ t, code.drop (pc + 1) = a :: b :: t := by
  refine ⟨code.drop (pc + 3), ?_⟩
  have h1 : pc + 1 < code.length := (List.getElem?_eq_some_iff.mp ha).1
  have h2 : pc + 2 < code.length := (List.getElem?_eq_some_iff.mp hb).1
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]
  simp only [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.some.injEq] at ha hb
  rw [ha, hb]

/-! ## The bridge -/

/-- Running a checked thread from a live instruction, with the stacks as its
certificate says, ends as the word's Spec says (or fails). -/
theorem run_sound {code : List Ins} {cert : List Cert} {out : Nat} {s r : List Cell} {u : Cell}
    (hc : ∀ pc, pc < code.length → stepOK code cert out pc = true) (hcalls : CallsMeet code cert) :
    ∀ (n pc : Nat) (ys zs : List Cell) (m : Mem) (e : Nat) (c : Cert),
      cert[pc]? = some c → c.live = true → ys.length = c.d → zs.length = c.r →
      Out s r u out 0 (run code n pc ⟨ys ++ s, zs ++ r, m, u, e⟩) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro pc ys zs m e c hcpc hlive hys hzs
  cases n with
  | zero => simp [run, S.fail, Out]
  | succ n =>
    have nextN : ∀ {n' p d' r' : Nat} (ys' zs' : List Cell) (m' : Mem) (e' : Nat), n' ≤ n →
        at? cert p d' r' = true → ys'.length = d' → zs'.length = r' →
        Out s r u out 0 (run code n' p ⟨ys' ++ s, zs' ++ r, m', u, e'⟩) := by
      intro n' p d' r' ys' zs' m' e' hn h h1 h2
      obtain ⟨c', hc', hl', hd', hr'⟩ := at?_spec h
      exact ih n' (by omega) p ys' zs' m' e' c' hc' hl' (by omega) (by omega)
    have next : ∀ {p d' r' : Nat} (ys' zs' : List Cell) (m' : Mem) (e' : Nat),
        at? cert p d' r' = true → ys'.length = d' → zs'.length = r' →
        Out s r u out 0 (run code n p ⟨ys' ++ s, zs' ++ r, m', u, e'⟩) :=
      fun ys' zs' m' e' => nextN ys' zs' m' e' (Nat.le_refl n)
    -- a callee meeting its Spec, from here, then on from p
    have callStep : ∀ (F : Sem) (p n' k j rk rj : Nat) (st : S), n' ≤ n → Spec F k j rk rj →
        k ≤ ys.length → rk ≤ zs.length → at? cert p (ys.length - k + j) (zs.length - rk + rj) = true →
        F ⟨ys ++ s, zs ++ r, m, u, e⟩ = .ok st → Out s r u out 0 (run code n' p st) := by
      intro F p n' k j rk rj st hn' hF hk hrk hnx hst
      have hf := hF (ys.take k) (zs.take rk) (ys.drop k ++ s) (zs.drop rk ++ r) m u e
        (by simp; omega) (by simp; omega)
      have e1 : ys.take k ++ (ys.drop k ++ s) = ys ++ s := by
        rw [← List.append_assoc, List.take_append_drop]
      have e2 : zs.take rk ++ (zs.drop rk ++ r) = zs ++ r := by
        rw [← List.append_assoc, List.take_append_drop]
      rw [e1, e2, hst] at hf
      obtain ⟨⟨ys2, hl2, hds⟩, ⟨ws, hwl, hrs⟩, hup⟩ := hf
      obtain ⟨ds', rs', m', u', e'⟩ := st
      simp only at hds hrs hup
      subst hds hrs hup
      have h := nextN (ys2 ++ ys.drop k) (ws ++ zs.drop rk) m' e' hn' hnx (by simp; omega) (by simp; omega)
      simpa only [List.append_assoc] using h
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
        have hm := callsMeet hcalls hcode hcpc
        cases hl : c.lk
        case false =>
          simp only [hl, Bool.false_eq_true, if_false] at hs
          simp only [run, hcode]
          exact next (v :: ys) zs m e hs (by simp; omega) hzs
        case true =>
          -- `['] word sem locked`: three steps as one
          simp only [hl, if_true] at hs
          cases hz1 : code[pc + 1]? with
          | none => simp [hz1] at hs
          | some i1 =>
          cases hz2 : code[pc + 2]? with
          | none => cases i1 <;> simp [hz1, hz2] at hs
          | some i2 =>
          cases i1 with
          | call P =>
            cases i2 with
            | call L =>
              simp only [hz1, hz2, Bool.and_eq_true, decide_eq_true_eq] at hs
              obtain ⟨⟨hk, hrk⟩, hn⟩ := hs
              obtain ⟨t, ht⟩ := drop_two hz1 hz2
              rw [ht] at hm
              simp only [InsMeets, hl, cond_true] at hm
              simp only [run, hcode]
              cases n with
              | zero => simp [run, S.fail, Out]
              | succ n =>
              simp only [run, hz1]
              split
              · rename_i s1 hs1
                cases n with
                | zero => simp [run, S.fail, Out]
                | succ n =>
                simp only [run, hz2]
                split
                · rename_i s2 hs2
                  exact callStep (seg3 v P L) (pc + 3) n c.k c.j c.rk c.rj s2 (by omega) hm (by omega)
                    (by omega) (by rw [hys, hzs]; exact hn) (by simp only [seg3, hs1, hs2])
                · simp [Out]
              · simp [Out]
            | _ => simp [hz1, hz2] at hs
          | _ => cases i2 <;> simp [hz1, hz2] at hs
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
        have hm := callsMeet hcalls hcode hcpc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
        obtain ⟨⟨hcl, hcz⟩, hs⟩ := hs
        simp only [hcl, hcz, InsMeets, cond_false] at hm
        cases hq : c.q
        case true =>
          -- `?dup`, then `0branch t` or `0=` and `0branch t`: as one step
          simp only [hq, cond_true] at hm
          simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at hs
          obtain ⟨hd1, hz⟩ := hs
          obtain ⟨x, ys', rfl⟩ : ∃ x ys', ys = x :: ys' := by
            cases ys with
            | nil => simp at hys; omega
            | cons x ys' => exact ⟨x, ys', rfl⟩
          simp only [List.length_cons] at hys
          simp only [run, hcode, List.cons_append, hm x (ys' ++ s) (zs ++ r) m u e]
          cases hz1 : code[pc + 1]? with
          | none => simp [hz1] at hz
          | some i1 =>
            cases i1 with
            | zbranch t =>
              simp only [hz1, Bool.and_eq_true] at hz
              obtain ⟨ht, hn⟩ := hz
              cases n with
              | zero => simp [run, S.fail, Out]
              | succ n =>
                simp only [run, hz1]
                by_cases hx : x = 0
                · simp only [hx, if_true]
                  exact nextN ys' zs m e (by omega) ht (by omega) hzs
                · simp only [hx, if_false]
                  exact nextN (x :: ys') zs m e (by omega) hn (by simp; omega) hzs
            | call g =>
              cases hz2 : code[pc + 2]? with
              | none => simp [hz1, hz2] at hz
              | some i2 =>
                cases i2 with
                | zbranch t =>
                  simp only [hz1, hz2, Bool.and_eq_true] at hz
                  obtain ⟨⟨hza, hn⟩, ht⟩ := hz
                  obtain ⟨c1, hc1, hc1z, hc1l⟩ :
                      ∃ c1, cert[pc + 1]? = some c1 ∧ c1.z = true ∧ c1.lk = false := by
                    unfold zAt at hza
                    split at hza
                    · rename_i c1 h
                      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hza
                      exact ⟨c1, h, hza.1, hza.2⟩
                    · contradiction
                  have hg := callsMeet hcalls hz1 hc1
                  simp only [hc1z, hc1l, InsMeets, cond_true, cond_false] at hg
                  cases n with
                  | zero => simp [run, S.fail, Out]
                  | succ n =>
                  have hg0 := hg 0 (ys' ++ s) (zs ++ r) m u e
                  have hgx := hg x (x :: (ys' ++ s)) (zs ++ r) m u e
                  cases n with
                  | zero =>
                    by_cases hx : x = 0
                    · subst hx; simp only [if_true, run, hz1, hg0]; simp [S.fail, Out]
                    · simp only [hx, if_false, run, hz1, hgx]; simp [S.fail, Out]
                  | succ n =>
                    by_cases hx : x = 0
                    · subst hx
                      simp only [if_true, run, hz1, hg0]
                      simp only [hz2]
                      rw [if_neg (by decide)]
                      exact nextN ys' zs m e (by omega) hn (by omega) hzs
                    · simp only [hx, if_false, run, hz1, hgx]
                      simp only [hz2, if_true]
                      exact nextN (x :: ys') zs m e (by omega) ht (by simp; omega) hzs
                | _ => simp [hz1, hz2] at hz
            | _ => simp [hz1] at hz
        case false =>
        simp only [hq, cond_false] at hm
        simp only [hq, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨⟨hk, hrk⟩, hn⟩ := hs
        simp only [run, hcode]
        split
        · rename_i st' hst
          exact callStep f (pc + 1) n c.k c.j c.rk c.rj st' (Nat.le_refl n) hm (by omega) (by omega)
            (by rw [hys, hzs]; exact hn) hst
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

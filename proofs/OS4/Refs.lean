import OS4.Words
import OS4.Loops
import OS4.Memory

/-!
# Reference definitions

The kernel has some hot spots in assembly; `core.fs` keeps their Forth
definitions as the reference. Here the reference words are proven to do
exactly what the model of each primitive does, for every input.
-/

namespace OS4.Refs
open OS4 OS4.Words

/-- `fill`'s loop, seen from its last byte. -/
theorem fillM_succ (c : BitVec 8) :
    ∀ (k : Nat) (m : Mem) (a : Cell),
      Prim.fillM (k + 1) m a c = upd (Prim.fillM k m a c) (a + BitVec.ofNat 64 k) c := by
  intro k
  induction k with
  | zero => intro m a; simp [Prim.fillM]
  | succ k ih =>
    intro m a
    rw [Prim.fillM, ih, ← Prim.fillM, add_assoc_ofNat]
  where add_assoc_ofNat : ∀ {a : Cell} {k : Nat}, a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
    intro a k
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- One pass of FILL-REF's loop body: store c at a + i, then step i. -/
theorem fill_step (n : Nat) (c a i u : Cell) (s r : List Cell) (M : Mem) (p : Cell) (e : Nat) :
    run «fill-ref».code (n + 6) 3 ⟨c :: a :: s, i :: u :: r, M, p, e⟩ =
      if i + 1 = u then run «fill-ref».code n 9 ⟨c :: a :: s, r, upd M (a + i) (c.setWidth 8), p, e⟩
      else run «fill-ref».code n 3 ⟨c :: a :: s, (i + 1) :: u :: r, upd M (a + i) (c.setWidth 8), p, e⟩ := by
  simp [forth, wr_one]

/-- The loop from pass k to the end, d + 1 passes later. -/
theorem fill_loop (c a u : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    ∀ (d k n : Nat), k + d + 1 = u.toNat →
      run «fill-ref».code (n + 6 * (d + 1)) 3
          ⟨c :: a :: s, BitVec.ofNat 64 k :: u :: r, Prim.fillM k m a (c.setWidth 8), p, e⟩ =
        run «fill-ref».code n 9 ⟨c :: a :: s, r, Prim.fillM u.toNat m a (c.setWidth 8), p, e⟩ := by
  have hu := u.isLt
  intro d
  induction d with
  | zero =>
    intro k n hk
    rw [fill_step, ← fillM_succ, hk]
    have : BitVec.ofNat 64 k + 1 = u := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp [this]
  | succ d ih =>
    intro k n hk
    rw [show n + 6 * (d + 1 + 1) = (n + 6 * (d + 1)) + 6 by omega, fill_step]
    have : BitVec.ofNat 64 k + 1 ≠ u := by
      intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega
    simp only [this, if_false]
    rw [← fillM_succ, show BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    exact ih (k + 1) n (by omega)

/-- FILL-REF does exactly what the FILL primitive does. -/
theorem fill_ref (c u a : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    «fill-ref» ⟨c :: u :: a :: s, r, m, p, e⟩ = Prim.fill ⟨c :: u :: a :: s, r, m, p, e⟩ := by
  by_cases h0 : u = 0
  · subst h0
    apply loopThread_eq _ _ 5 _ (by simp [forth, Prim.fillM]) (by simp [outOfFuel])
  · have hN : u.toNat ≠ 0 := by intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simp [h])
    apply loopThread_eq _ _ ((2 + 6 * ((u.toNat - 1) + 1)) + 3) _ _ (by simp [forth])
    have start : ∀ x, run «fill-ref».code (x + 3) 0 ⟨c :: u :: a :: s, r, m, p, e⟩ =
        run «fill-ref».code x 3 ⟨c :: a :: s, BitVec.ofNat 64 0 :: u :: r, Prim.fillM 0 m a (c.setWidth 8), p, e⟩ := by
      intro x; simp [forth, Prim.fillM, Ne.symm h0]
    rw [start, fill_loop c a u s r m p e (u.toNat - 1) 0 2 (by omega)]
    simp [forth]

end OS4.Refs

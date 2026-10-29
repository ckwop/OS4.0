import OS4.Machine

/-!
# Memory

What a read sees after a write: the same cell gives back what was written, and
a write elsewhere (at least 8 bytes away, in both directions round the 64-bit
address space) leaves it alone.
-/

namespace OS4

theorem upd_same (m : Mem) (a : Cell) (b : BitVec 8) : upd m a b a = b := by simp [upd]
theorem upd_other (m : Mem) (a x : Cell) (b : BitVec 8) (h : x ≠ a) : upd m a b x = m x := by
  simp [upd, h]

theorem wr_one (m : Mem) (a v : Cell) : wr m a 1 v = upd m a (v.setWidth 8) := rfl
theorem rd_one (m : Mem) (a : Cell) : rd m a 1 = (m a).setWidth 64 := by
  simp [rd]

/-- A cell reads back what was stored in it. -/
theorem rd_wr_same (m : Mem) (a v : Cell) : rd (wr m a 8 v) a 8 = v := by
  simp only [rd, wr, upd]
  bv_decide

theorem add_ofNat_succ (a : Cell) (j : Nat) :
    a + BitVec.ofNat 64 (j + 1) = a + 1 + BitVec.ofNat 64 j := by
  bv_omega

/-- A write of n bytes at a leaves every other byte alone. -/
theorem wr_apply_other (x : Cell) :
    ∀ (n : Nat) (m : Mem) (a v : Cell), (∀ j, j < n → x ≠ a + BitVec.ofNat 64 j) → wr m a n v x = m x := by
  intro n
  induction n with
  | zero => intro m a v _; rfl
  | succ n ih =>
    intro m a v h
    simp only [wr]
    rw [ih]
    · have := h 0 (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      simp [upd, this]
    · intro j hj
      rw [← add_ofNat_succ]
      exact h (j + 1) (by omega)

/-- A read of n bytes at b sees only those bytes. -/
theorem rd_congr (m1 m2 : Mem) :
    ∀ (n : Nat) (b : Cell), (∀ i, i < n → m1 (b + BitVec.ofNat 64 i) = m2 (b + BitVec.ofNat 64 i)) →
      rd m1 b n = rd m2 b n := by
  intro n
  induction n with
  | zero => intro b _; rfl
  | succ n ih =>
    intro b h
    simp only [rd]
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    rw [h0, ih (b + 1)]
    intro i hi
    rw [← add_ofNat_succ]
    exact h (i + 1) (by omega)

/-- A store at least a cell away leaves a cell alone. -/
theorem rd_wr_other (m : Mem) (a b v : Cell) (h1 : 8 ≤ b - a) (h2 : 8 ≤ a - b) :
    rd (wr m a 8 v) b 8 = rd m b 8 := by
  have apart : ∀ i j : Cell, i < 8 → j < 8 → b + i ≠ a + j := by
    intro i j hi hj
    bv_decide
  apply rd_congr
  intro i hi
  apply wr_apply_other
  intro j hj
  have small : ∀ n : Nat, n < 8 → BitVec.ofNat 64 n < 8 := by
    intro n hn
    simp only [BitVec.lt_def, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hn (by decide))]
    exact hn
  exact apart _ _ (small i hi) (small j hj)

end OS4

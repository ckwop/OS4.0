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

/-- A store at least a cell away leaves a cell alone. -/
theorem rd_wr_other (m : Mem) (a b v : Cell) (h1 : 8 ≤ b - a) (h2 : 8 ≤ a - b) :
    rd (wr m a 8 v) b 8 = rd m b 8 := by
  simp only [rd, wr, upd]
  bv_decide

end OS4

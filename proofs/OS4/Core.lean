import OS4.Words

/-!
# core.fs

Each word does what its stack-effect comment says, for every input. Stacks are
written TOS first: `( a b c -- b c a )` takes `c :: b :: a :: s` to
`a :: c :: b :: s`. The return stack `r` is left as it was.
-/

namespace OS4.Core
open OS4 OS4.Words

variable (s r : List Cell)

-- ---- Stack

theorem rot (a b c : Cell) : «rot» ⟨c :: b :: a :: s, r⟩ = .ok ⟨a :: c :: b :: s, r⟩ := by forth_run
theorem nrot (a b c : Cell) : «-rot» ⟨c :: b :: a :: s, r⟩ = .ok ⟨b :: a :: c :: s, r⟩ := by forth_run
theorem nip (a b : Cell) : «nip» ⟨b :: a :: s, r⟩ = .ok ⟨b :: s, r⟩ := by forth_run
theorem tuck (a b : Cell) : «tuck» ⟨b :: a :: s, r⟩ = .ok ⟨b :: a :: b :: s, r⟩ := by forth_run
theorem two_dup (a b : Cell) : «2dup» ⟨b :: a :: s, r⟩ = .ok ⟨b :: a :: b :: a :: s, r⟩ := by forth_run
theorem two_drop (a b : Cell) : «2drop» ⟨b :: a :: s, r⟩ = .ok ⟨s, r⟩ := by forth_run
theorem two_swap (a b c d : Cell) :
    «2swap» ⟨d :: c :: b :: a :: s, r⟩ = .ok ⟨b :: a :: d :: c :: s, r⟩ := by forth_run
theorem two_over (a b c d : Cell) :
    «2over» ⟨d :: c :: b :: a :: s, r⟩ = .ok ⟨b :: a :: d :: c :: b :: a :: s, r⟩ := by forth_run

-- ---- Arithmetic, modulo 2^64

theorem one_plus (n : Cell) : «1+» ⟨n :: s, r⟩ = .ok ⟨(n + 1) :: s, r⟩ := by forth_run
theorem one_minus (n : Cell) : «1-» ⟨n :: s, r⟩ = .ok ⟨(n - 1) :: s, r⟩ := by forth_run
theorem negate (n : Cell) : «negate» ⟨n :: s, r⟩ = .ok ⟨(-n) :: s, r⟩ := by forth_run
theorem two_star (n : Cell) : «2*» ⟨n :: s, r⟩ = .ok ⟨(n * 2) :: s, r⟩ := by
  forth_run; bv_decide
theorem cells (n : Cell) : «cells» ⟨n :: s, r⟩ = .ok ⟨(n * 8) :: s, r⟩ := by
  forth_run; bv_decide
theorem cell_plus (a : Cell) : «cell+» ⟨a :: s, r⟩ = .ok ⟨(a + 8) :: s, r⟩ := by forth_run
theorem char_plus (a : Cell) : «char+» ⟨a :: s, r⟩ = .ok ⟨(a + 1) :: s, r⟩ := by forth_run

-- ---- Comparison: each gives a well-formed flag

theorem zero_ne (x : Cell) : «0<>» ⟨x :: s, r⟩ = .ok ⟨flag (x != 0) :: s, r⟩ := by forth_run
theorem ne (a b : Cell) : «<>» ⟨b :: a :: s, r⟩ = .ok ⟨flag (a != b) :: s, r⟩ := by forth_run
theorem gt (a b : Cell) : «>» ⟨b :: a :: s, r⟩ = .ok ⟨flag (b.slt a) :: s, r⟩ := by forth_run
theorem ugt (a b : Cell) : «u>» ⟨b :: a :: s, r⟩ = .ok ⟨flag (b.ult a) :: s, r⟩ := by forth_run
theorem zero_gt (n : Cell) : «0>» ⟨n :: s, r⟩ = .ok ⟨flag ((0 : Cell).slt n) :: s, r⟩ := by forth_run

-- ---- Words with branches

theorem qdup_zero : «?dup» ⟨0 :: s, r⟩ = .ok ⟨0 :: s, r⟩ := by forth_run
theorem qdup_nonzero (x : Cell) (h : x ≠ 0) : «?dup» ⟨x :: s, r⟩ = .ok ⟨x :: x :: s, r⟩ := by
  forth_run

theorem abs (n : Cell) :
    «abs» ⟨n :: s, r⟩ = .ok ⟨(if n.slt 0 then -n else n) :: s, r⟩ := by
  forth_auto

theorem min (a b : Cell) :
    Words.«min» ⟨b :: a :: s, r⟩ = .ok ⟨(if a.slt b then a else b) :: s, r⟩ := by
  forth_auto

theorem max (a b : Cell) :
    Words.«max» ⟨b :: a :: s, r⟩ = .ok ⟨(if a.slt b then b else a) :: s, r⟩ := by
  forth_auto

/-- WITHIN is the usual one-comparison trick: for lo ≤ hi it is lo ≤ n < hi. -/
theorem within (n lo hi : Cell) (h : lo.sle hi) :
    «within» ⟨hi :: lo :: n :: s, r⟩ = .ok ⟨flag (lo.sle n && n.slt hi) :: s, r⟩ := by
  forth_run
  have : (n - lo).ult (hi - lo) = (lo.sle n && n.slt hi) := by bv_decide
  simp [this]

-- ---- Division: floored, as the standard's FM/MOD

/-- The one case the standard leaves ambiguous: the quotient 2^63 does not fit,
and `sdiv` wraps it to the most negative number. -/
theorem div_overflow :
    «/» ⟨[-1, BitVec.intMin 64], []⟩ = .ok ⟨[BitVec.intMin 64], []⟩ := by
  rfl

theorem div_by_zero (n : Cell) : «/» ⟨0 :: n :: s, r⟩ = .error .divZero := by forth_run

end OS4.Core

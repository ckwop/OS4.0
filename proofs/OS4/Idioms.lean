import OS4.Footprint
import OS4.Words.Core

/-!
# Idioms the certificates know

`?dup` just before a `0branch` (the `?dup if` idiom), or before `0=` and a
`0branch` (`?dup 0= if`): its depth afterwards depends on its input, so a
certificate takes them together (`QDup`, `ZEq`), and needs these to know
that the words compiled as `?dup` and `0=` do what those say.
-/

namespace OS4.Words
open OS4

theorem «?dup».qdup : QDup «?dup» := by
  intro x s r m u e
  simp only [«?dup», «?dup».code, thread, run, forth, List.length_cons, List.length_nil,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  split <;> simp_all

/-- `0=`, which the `?dup 0= if` idiom needs. -/
theorem Prim.zequal_zeq : ZEq Prim.zequal := by
  intro x s r m u e
  by_cases hx : x = 0 <;> simp [forth, hx]

end OS4.Words

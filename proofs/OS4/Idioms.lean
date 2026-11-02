import OS4.Footprint
import OS4.Words.Core

/-!
# Idioms the certificates know

`?dup` just before a `0branch` (the `?dup if` idiom): its depth afterwards
depends on its input, so a certificate takes the two together (`QDup`), and
needs this to know that the word compiled as `?dup` does what `QDup` says.
-/

namespace OS4.Words
open OS4

theorem «?dup».qdup : QDup «?dup» := by
  intro x s r m u e
  simp only [«?dup», «?dup».code, thread, run, forth, List.length_cons, List.length_nil,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  split <;> simp_all

end OS4.Words

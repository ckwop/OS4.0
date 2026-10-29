import OS4.Machine

/-!
# Reasoning about loops

A word with a loop is a `loopThread`: the result of running its thread with
enough fuel. These lemmas let a proof pick the fuel: `run_mono` says more fuel
never changes an answer, so `loopThread_eq` turns any terminating `run` into
the word's result. A loop is then proven one iteration at a time (by symbolic
execution, with `run_add`'s fuel arithmetic) and by induction on iterations.
-/

namespace OS4

/-- More fuel never changes a result other than running out of it. -/
theorem run_mono (code : List Ins) :
    ∀ (n k pc : Nat) (s : S), ¬ outOfFuel (run code n pc s) →
      run code (n + k) pc s = run code n pc s := by
  intro n
  induction n with
  | zero => intro k pc s h; simp [run, S.fail, outOfFuel] at h
  | succ n ih =>
    intro k pc s h
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [run] at h ⊢
    split <;> (try rfl)
    all_goals (repeat' split) <;> (try rfl) <;> simp_all

/-- A loop word's result is that of any run with enough fuel. -/
theorem loopThread_eq (code : List Ins) (s : S) (n : Nat) (r : Except Fail S)
    (h : run code n 0 s = r) (hr : ¬ outOfFuel r) : loopThread code s = r := by
  have ex : ∃ n, ¬ outOfFuel (run code n 0 s) := ⟨n, h ▸ hr⟩
  unfold loopThread
  rw [dif_pos ex]
  have hc := Classical.choose_spec ex
  have h1 := run_mono code (Classical.choose ex) n 0 s hc
  have h2 := run_mono code n (Classical.choose ex) 0 s (h ▸ hr)
  rw [Nat.add_comm] at h2
  rw [← h1, h2, h]

end OS4

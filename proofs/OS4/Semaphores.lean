import OS4.Words
import OS4.Loops
import OS4.Memory

/-!
# Semaphores

`locked` ( i*x xt sem -- j*x ) runs xt holding a semaphore, and releases it
however xt ends (core.fs; DECISIONS.md #76). Proven here: if the semaphore is
free when LOCKED starts, it is free again afterwards, whether xt returns or
fails with anything CATCH catches, provided xt leaves the semaphore alone.
-/

namespace OS4.Semaphores
open OS4 OS4.Words

/-- xt leaves the semaphore at a alone (both its cells: the holder and the
count), and, when it returns, the return stack and the user area too. -/
def Keeps (xt a : Cell) : Prop :=
  ∀ st : S,
    match dispatch xt st with
    | .ok st' => rd st'.mem a 8 = rd st.mem a 8 ∧ rd st'.mem (a + 8) 8 = rd st.mem (a + 8) 8 ∧
                 st'.rs = st.rs ∧ st'.up = st.up
    | .error f => rd f.mem a 8 = rd st.mem a 8 ∧ rd f.mem (a + 8) 8 = rd st.mem (a + 8) 8

theorem apart (a : Cell) : 8 ≤ a + 8 - a ∧ 8 ≤ a - (a + 8) := by bv_decide

/-- GET on a free semaphore takes it: holder this task, count 1. -/
theorem get_free (a : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hfree : rd m a 8 = 0) (hu : u ≠ 0) :
    «get» ⟨a :: s, r, m, u, e⟩ = .ok ⟨s, r, wr (wr m a 8 u) (a + 8) 8 1, u, e⟩ := by
  have hu' : (0 : Cell) ≠ u := Ne.symm hu
  apply loopThread_eq _ _ 16 _ _ (by simp [outOfFuel])
  simp [forth, hfree, hu']

/-- RELEASE by its holder, with count 1, frees the semaphore. -/
theorem release_last (a : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hheld : rd m a 8 = u) (hcount : rd m (a + 8) 8 = 1) :
    ∃ m', «release» ⟨a :: s, r, m, u, e⟩ = .ok ⟨s, r, m', u, e⟩ ∧ rd m' a 8 = 0 := by
  have h := apart a
  refine ⟨_, ?_, rd_wr_same _ _ _⟩
  simp [forth, hheld, hcount, rd_wr_same]

/-- However xt ends (unless it never does, or ends the run with BYE), LOCKED
leaves a semaphore that was free, free. -/
theorem locked_releases (xt a : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hfree : rd m a 8 = 0) (hu : u ≠ 0) (hx : Keeps xt a) :
    match «locked» ⟨a :: xt :: s, r, m, u, e⟩ with
    | .ok st => rd st.mem a 8 = 0
    | .error f => f.err.code.isSome → rd f.mem a 8 = 0 := by
  have ⟨h1, h2⟩ := apart a
  have held : rd (wr (wr m a 8 u) (a + 8) 8 1) a 8 = u := by
    rw [rd_wr_other _ _ _ _ h2 h1, rd_wr_same]
  have count : rd (wr (wr m a 8 u) (a + 8) 8 1) (a + 8) 8 = 1 := rd_wr_same _ _ _
  have hk := hx ⟨s, a :: r, wr (wr m a 8 u) (a + 8) 8 1, u, e⟩
  simp only [«locked», thread, run, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Prim.dup, Prim.tor, get_free a _ _ m u e hfree hu,
    catchM, Prim.rfrom]
  split
  · rename_i st hd
    rw [hd] at hk
    obtain ⟨ha, hc, hrs, hup⟩ := hk
    obtain ⟨m', hrel, hm'⟩ := release_last a st.ds r st.mem u st.ext (by rw [ha, held]) (by rw [hc, count])
    simp only at hrs hup
    obtain ⟨ds, rs, mem, up, ext⟩ := st
    simp only at hrs hup hrel ⊢
    subst hrs hup
    simp [hrel, throwM, hm']
  · rename_i f hd
    rw [hd] at hk
    obtain ⟨ha, hc⟩ := hk
    split
    · rename_i n hn
      obtain ⟨m', hrel, hm'⟩ := release_last a _ r f.mem u f.ext (by rw [ha, held]) (by rw [hc, count])
      simp only [hrel, throwM]
      split <;> simp [hm']
    · rename_i hn
      simp [hn]

end OS4.Semaphores

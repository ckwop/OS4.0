import OS4.Words.Interpreter
import OS4.Loops
import OS4.Memory

/-!
# Semaphores, and what a stopped task gives up

Part of milestone V6 (docs/verification.md). Like `Refs.lean`, this file must
not open `OS4.Words`, where the Forth word FORTH shadows the `forth` simp set.

* `locked` ( i*x xt sem -- j*x ) runs xt holding a semaphore, and releases it
  however xt ends (core.fs; DECISIONS.md #76): `locked_releases`.
* A task can be stopped anywhere, by the watchdog or an error, even inside
  `get` before LOCKED's catch frame exists. So whatever ends a task's work
  then runs `release-all` (DECISIONS.md #116): `retire`, which ends a task's
  life (`run-task`, and `(quit)` for any task but the console), the REPL's
  `reset`, and `restarting`. `release_all` proves that it frees every
  semaphore on the chain that this task holds, leaves the others as they
  were, and writes nothing else; `unclaim_frees` that `unclaim` gives up the
  dictionary. `cleanup_wired` checks where they are called.

Trusted, not proven here: that the cleanup itself finishes before the
watchdog could stop it again. THROW gives its catcher a fresh allowance
(core.fs), and the chain holds a handful of semaphores, made at boot.
-/

namespace OS4.Semaphores
open OS4

/-! ## LOCKED -/

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
    Words.«get» ⟨a :: s, r, m, u, e⟩ = .ok ⟨s, r, wr (wr m a 8 u) (a + 8) 8 1, u, e⟩ := by
  have hu' : ¬ (0#64 = u) := Ne.symm hu
  apply loopThread_eq _ _ 16 _ _ (by simp [outOfFuel])
  simp [forth, hfree, hu']

/-- RELEASE by its holder, with count 1, frees the semaphore. -/
theorem release_last (a : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hheld : rd m a 8 = u) (hcount : rd m (a + 8) 8 = 1) :
    ∃ m', Words.«release» ⟨a :: s, r, m, u, e⟩ = .ok ⟨s, r, m', u, e⟩ ∧ rd m' a 8 = 0 := by
  have hc : rd m (a + 8#64) 8 + 18446744073709551615#64 = 0#64 := by
    rw [show a + 8#64 = a + 8 from rfl, hcount]; decide
  have h0 : rd (wr m (a + 8#64) 8 0#64) (a + 8#64) 8 = 0#64 := rd_wr_same _ _ _
  refine ⟨wr (wr m (a + 8#64) 8 0#64) a 8 0#64, ?_, rd_wr_same _ _ _⟩
  -- in two passes: one simp over the whole thread is too deep for the kernel
  set_option simprocs false in
  simp only [forth, hheld, hc, h0, List.getElem?_cons_zero, List.getElem?_cons_succ, List.length_cons,
    List.length_nil, ite_true, ite_false, if_pos, BitVec.ofNat_eq_ofNat]
  all_goals simp [h0]

/-- However xt ends (unless it never does, or ends the run with BYE), LOCKED
leaves a semaphore that was free, free. -/
theorem locked_releases (xt a : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hfree : rd m a 8 = 0) (hu : u ≠ 0) (hx : Keeps xt a) :
    match Words.«locked» ⟨a :: xt :: s, r, m, u, e⟩ with
    | .ok st => rd st.mem a 8 = 0
    | .error f => f.err.code.isSome → rd f.mem a 8 = 0 := by
  have ⟨h1, h2⟩ := apart a
  have held : rd (wr (wr m a 8 u) (a + 8) 8 1) a 8 = u := by
    rw [rd_wr_other _ _ _ _ h2 h1, rd_wr_same]
  have count : rd (wr (wr m a 8 u) (a + 8) 8 1) (a + 8) 8 = 1 := rd_wr_same _ _ _
  have hk := hx ⟨s, a :: r, wr (wr m a 8 u) (a + 8) 8 1, u, e⟩
  simp only [Words.«locked», Words.«locked».code, thread, run, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Prim.dup, Prim.tor,
    get_free a _ _ m u e hfree hu, catchM, Prim.rfrom]
  generalize dispatch xt ⟨s, a :: r, wr (wr m a 8 u) (a + 8) 8 1, u, e⟩ = res at hk ⊢
  cases res with
  | ok st =>
    obtain ⟨ds, rs, mem, up, ext⟩ := st
    obtain ⟨ha, hc, hrs, hup⟩ := hk
    simp only at ha hc hrs hup
    subst hrs hup
    obtain ⟨m', hrel, hm'⟩ := release_last a (0#64 :: ds) r mem up ext (by rw [ha, held]) (by rw [hc, count])
    simp [hrel, throwM, hm']
  | error f =>
    obtain ⟨ha, hc⟩ := hk
    simp only at ha hc
    cases hn : f.err.code with
    | some n =>
      obtain ⟨m', hrel, hm'⟩ := release_last a (n :: List.map (junk f.ext) (List.range s.length)) r
        f.mem u f.ext (by rw [ha, held]) (by rw [hc, count])
      by_cases h0 : n = 0#64
      · subst h0
        simp [hn, hrel, throwM, hm']
      · simp [hn, hrel, throwM, h0, hm']
    | none => simp [hn]

/-! ## RELEASE-ALL

`semaphore` lays out three cells, holder, count and link, and puts the new
one at the head of the chain in the variable `semaphores`. -/

/-- What RELEASE-ALL does to one semaphore: if task u holds it, both its
holder and its count become 0. -/
def clear (u : Cell) (m : Mem) (c : Cell) : Mem :=
  if rd m c 8 = u then wr (wr m c 8 0) (c + 8) 8 0 else m

/-- The chain from a holds the semaphores l, newest first: each links (its
third cell) to the next, and the last to 0. -/
def Chain (m : Mem) : Cell → List Cell → Prop
  | a, [] => a = 0
  | a, c :: l => a = c ∧ c ≠ 0 ∧ Chain m (rd m (c + 16) 8) l

/-- Two semaphores' cells do not overlap. -/
def Apart (b c : Cell) : Prop := 24 ≤ c - b ∧ 24 ≤ b - c

theorem chain_congr (m m' : Mem) : ∀ (l : List Cell) (a : Cell),
    (∀ c ∈ l, rd m' (c + 16) 8 = rd m (c + 16) 8) → Chain m a l → Chain m' a l
  | [], _, _, h => h
  | c :: l, _, hl, ⟨ha, hc, hn⟩ => by
    refine ⟨ha, hc, ?_⟩
    rw [hl c (by simp)]
    exact chain_congr m m' l _ (fun x hx => hl x (by simp [hx])) hn

/-- Clearing a semaphore leaves every link alone: its own, and others'. -/
theorem clear_link (u : Cell) (m : Mem) (b c : Cell) (h : Apart b c ∨ c = b) :
    rd (clear u m b) (c + 16) 8 = rd m (c + 16) 8 := by
  unfold clear
  split
  · rcases h with ⟨h1, h2⟩ | rfl
    · rw [rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide),
        rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide)]
    · rw [rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide),
        rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide)]
  · rfl

/-- Clearing one semaphore leaves another's holder and count alone. -/
theorem clear_other (u : Cell) (m : Mem) (b c : Cell) (h : Apart b c) :
    rd (clear u m b) c 8 = rd m c 8 ∧ rd (clear u m b) (c + 8) 8 = rd m (c + 8) 8 := by
  obtain ⟨h1, h2⟩ := h
  unfold clear
  split
  · constructor
    · rw [rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide),
        rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide)]
    · rw [rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide),
        rd_wr_other _ _ _ _ (by bv_decide) (by bv_decide)]
  · exact ⟨rfl, rfl⟩

theorem foldl_clear_other (u c : Cell) : ∀ (l : List Cell) (m : Mem), (∀ d ∈ l, Apart d c) →
    rd (l.foldl (clear u) m) c 8 = rd m c 8 ∧ rd (l.foldl (clear u) m) (c + 8) 8 = rd m (c + 8) 8
  | [], _, _ => ⟨rfl, rfl⟩
  | d :: l, m, h => by
    obtain ⟨ih1, ih2⟩ := foldl_clear_other u c l (clear u m d) (fun x hx => h x (by simp [hx]))
    obtain ⟨h1, h2⟩ := clear_other u m d c (h d (by simp))
    exact ⟨ih1.trans h1, ih2.trans h2⟩

/-- RELEASE-ALL's loop, from its head (`?dup`, at 2) with a on the stack. -/
theorem release_all_run (u : Cell) (r : List Cell) (hu : u ≠ 0) : ∀ (l : List Cell) (a : Cell)
    (s : List Cell) (m : Mem) (e : Nat), Chain m a l → l.Pairwise Apart →
    ∃ n, run Words.«release-all».code n 2 ⟨a :: s, r, m, u, e⟩ = .ok ⟨s, r, l.foldl (clear u) m, u, e⟩
  | [], a, s, m, e, ha, _ => ⟨3, by subst ha; simp [forth]⟩
  | c :: l, a, s, m, e, ⟨ha, hc, hn⟩, hp => by
    subst ha
    rw [List.pairwise_cons] at hp
    have hn' : Chain (clear u m a) (rd (clear u m a) (a + 16) 8) l := by
      rw [clear_link u m a a (Or.inr rfl)]
      exact chain_congr m _ l _ (fun x hx => clear_link u m a x (Or.inl (hp.1 x hx))) hn
    obtain ⟨n, hrun⟩ := release_all_run u r hu l _ s (clear u m a) e hn' hp.2
    have hu' : ¬ (0#64 = u) := Ne.symm hu
    have hc' : ¬ (a = 0#64) := hc
    rw [List.foldl_cons]
    by_cases hh : rd m a 8 = u
    · refine ⟨n + 19, ?_⟩
      rw [← hrun]
      simp [forth, hc', hh, hu', clear]
    · refine ⟨n + 12, ?_⟩
      rw [← hrun]
      simp [forth, hc', hh, clear]

/-- RELEASE-ALL clears, of the semaphores on the chain, those this task holds,
and nothing else: no stack item, no other memory, no outside event. -/
theorem release_all (u : Cell) (hu : u ≠ 0) (l : List Cell) (s r : List Cell) (m : Mem) (e : Nat)
    (hc : Chain m (rd m (wordAddr "semaphores" + 8) 8) l) (hp : l.Pairwise Apart) :
    Words.«release-all» ⟨s, r, m, u, e⟩ = .ok ⟨s, r, l.foldl (clear u) m, u, e⟩ := by
  obtain ⟨n, h⟩ := release_all_run u r hu l _ s m e hc hp
  apply loopThread_eq _ _ (n + 2) _ _ (by simp [outOfFuel])
  rw [← h]
  simp [forth]

/-- Afterwards this task holds none of them. -/
theorem foldl_clear_free (u : Cell) (hu : u ≠ 0) : ∀ (l : List Cell) (m : Mem), l.Pairwise Apart →
    ∀ c ∈ l, rd (l.foldl (clear u) m) c 8 ≠ u
  | [], _, _, _, h => by simp at h
  | d :: l, m, hp, c, hc => by
    rw [List.pairwise_cons] at hp
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [(foldl_clear_other u c l (clear u m c) (fun x hx => ⟨(hp.1 x hx).2, (hp.1 x hx).1⟩)).1]
      unfold clear
      split
      · have ⟨h1, h2⟩ := apart c
        rw [rd_wr_other _ _ _ _ h2 h1, rd_wr_same]
        exact Ne.symm hu
      · assumption
    · exact foldl_clear_free u hu l _ hp.2 c hc

/-- And memory outside the semaphores' holders and counts is as it was. -/
theorem foldl_clear_frame (u x : Cell) : ∀ (l : List Cell) (m : Mem), (∀ c ∈ l, 16 ≤ x - c) →
    l.foldl (clear u) m x = m x
  | [], _, _ => rfl
  | c :: l, m, h => by
    rw [List.foldl_cons, foldl_clear_frame u x l _ (fun d hd => h d (by simp [hd]))]
    have hx := h c (by simp)
    unfold clear
    split
    · have small : ∀ n : Nat, n < 8 → BitVec.ofNat 64 n < 8 := by
        intro n hn
        simp only [BitVec.lt_def, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.lt_trans hn (by decide))]
        exact hn
      have near : ∀ j : Cell, j < 8 → x ≠ c + j ∧ x ≠ c + 8 + j := by
        intro j hj
        constructor <;> bv_decide
      rw [wr_apply_other x 8 _ _ _ (fun j hj => (near _ (small j hj)).2),
        wr_apply_other x 8 _ _ _ (fun j hj => (near _ (small j hj)).1)]
    · rfl

/-! ## UNCLAIM -/

/-- UNCLAIM gives up the dictionary if this task holds it, and changes nothing else. -/
theorem unclaim_frees (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    Words.«unclaim» ⟨s, r, m, u, e⟩ =
      .ok ⟨s, r, if rd m (kernelAddr "dict-owner") 8 = u then wr m (kernelAddr "dict-owner") 8 0 else m, u, e⟩ := by
  by_cases h : rd m (kernelAddr "dict-owner") 8 = u <;> simp [forth, h]

/-! ## Where the cleanup runs -/

/-- RETIRE starts by giving up the dictionary and the semaphores; RUN-TASK
retires when its work ends however it ends, and `(quit)` retires any task but
the console; the REPL's RESET and RESTARTING release semaphores too. -/
theorem cleanup_wired :
    Words.«retire».code.take 2 = [.call Words.«unclaim», .call Words.«release-all»] ∧
    Words.«run-task».code[7]? = some (.call Words.«retire») ∧
    Words.«(quit)».code[4]? = some (.call Words.«retire») ∧
    Words.«reset».code[13]? = some (.call Words.«unclaim») ∧
    Words.«reset».code[14]? = some (.call Words.«release-all») ∧
    Words.«restarting».code[8]? = some (.call Words.«release-all») := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end OS4.Semaphores

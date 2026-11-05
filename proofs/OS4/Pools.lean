import OS4.Words.NetTcp
import OS4.Loops
import OS4.Memory

/-!
# The connection pool (V4)

Live connections and recycled ones sit on two lists linked through each
connection's first cell (`c.link`). `unlink` takes a connection off a list:
here it is proven to leave exactly the list without it, whatever the list
holds, provided the list ends and its cells are apart. That is the step on
which every closing path's return of its slot rests (`(free-conn)`).
-/

namespace OS4.Pools
open OS4

/-- The list xs, linked from the cell at a through each element's first cell,
ending in 0. -/
def Chain (m : Mem) (a : Cell) : List Cell → Prop
  | [] => rd m a 8 = 0
  | x :: xs => rd m a 8 = x ∧ x ≠ 0 ∧ Chain m x xs

/-- `unlink`'s memory: the cell before c's first occurrence takes c's link. -/
def unlinkM (m : Mem) (c : Cell) : Cell → List Cell → Mem
  | _, [] => m
  | a, x :: xs => if x = c then wr m a 8 (rd m c 8) else unlinkM m c x xs

/-- Steps `unlink` takes over a list: 11 a connection it passes, 15 for the
one it finds, 5 at the end. -/
def unlinkFuel (c : Cell) : List Cell → Nat
  | [] => 5
  | x :: xs => if x = c then 15 else 11 + unlinkFuel c xs

set_option maxHeartbeats 4000000 in
theorem unlink_run (c : Cell) (s r : List Cell) (u : Cell) (e : Nat) :
    ∀ (xs : List Cell) (a : Cell) (m : Mem) (n : Nat), Chain m a xs →
      run Words.«unlink».code (unlinkFuel c xs + n) 0 ⟨a :: c :: s, r, m, u, e⟩ =
        .ok ⟨s, r, unlinkM m c a xs, u, e⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro a m n h
    simp only [Chain] at h
    simp only [unlinkFuel, unlinkM]
    rw [show 5 + n = n + 1 + 1 + 1 + 1 + 1 by omega]
    simp [forth, h]
  | cons x xs ih =>
    intro a m n h
    obtain ⟨hx, hx0, hc⟩ := h
    by_cases hxc : x = c
    · subst hxc
      simp only [unlinkFuel, unlinkM, if_true]
      rw [show 15 + n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      simp [forth, hx, hx0]
      exact fun h => absurd h hx0
    · simp only [unlinkFuel, unlinkM, if_neg hxc]
      rw [show 11 + unlinkFuel c xs + n = (unlinkFuel c xs + n) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
        by omega]
      have step := ih x m n hc
      simp [forth, hx, hx0, hxc] at step ⊢
      rw [if_neg (by simpa using hx0)]
      exact step

/-- `unlink` ends, with that memory, on any list that ends. -/
theorem unlink_eq (c a : Cell) (xs : List Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (h : Chain m a xs) :
    Words.«unlink» ⟨a :: c :: s, r, m, u, e⟩ = .ok ⟨s, r, unlinkM m c a xs, u, e⟩ := by
  have hr := unlink_run c s r u e xs a m 0 h
  exact loopThread_eq _ _ _ _ hr (by simp [outOfFuel])

/-- Two cells that do not overlap. -/
def Apart (x y : Cell) : Prop := 8 ≤ x - y ∧ 8 ≤ y - x

/-- A store to a cell apart from every cell of a chain leaves the chain. -/
theorem chain_wr (q v : Cell) : ∀ (ys : List Cell) (b : Cell) (m : Mem),
    Chain m b ys → (∀ y ∈ b :: ys, Apart q y) → Chain (wr m q 8 v) b ys := by
  intro ys
  induction ys with
  | nil =>
    intro b m h hq
    have hb := hq b (by simp)
    simp only [Chain] at h ⊢
    rw [rd_wr_other m q b v hb.2 hb.1]; exact h
  | cons y ys ih =>
    intro b m h hq
    obtain ⟨hy, hy0, hc⟩ := h
    have hb := hq b (by simp)
    refine ⟨by rw [rd_wr_other m q b v hb.2 hb.1]; exact hy, hy0, ?_⟩
    exact ih y m hc fun z hz => hq z (List.mem_cons_of_mem b hz)

/-- `unlink` stores only into a cell of the chain it walks. -/
theorem unlinkM_rd (m : Mem) (c a : Cell) : ∀ (xs : List Cell) (b : Cell),
    (∀ y ∈ b :: xs, Apart a y) → rd (unlinkM m c b xs) a 8 = rd m a 8 := by
  intro xs
  induction xs with
  | nil => intro b _; rfl
  | cons y ys ih =>
    intro b hb
    simp only [unlinkM]
    split
    · have h := hb b (by simp)
      exact rd_wr_other m b a _ h.1 h.2
    · exact ih y fun z hz => hb z (List.mem_cons_of_mem b hz)

/-- `unlink` takes c off a chain: what is left is the chain without it. The
chain's cells (the list's head cell and each element's) must be apart. -/
theorem unlink_chain (c : Cell) : ∀ (xs : List Cell) (a : Cell) (m : Mem),
    Chain m a xs → (a :: xs).Pairwise Apart → c ∈ xs →
      Chain (unlinkM m c a xs) a (xs.erase c) := by
  intro xs
  induction xs with
  | nil => intro a m _ _ hc; simp at hc
  | cons x xs ih =>
    intro a m h hp hc
    obtain ⟨hx, hx0, hch⟩ := h
    have hpa := List.pairwise_cons.mp hp
    by_cases hxc : x = c
    · subst hxc
      simp only [unlinkM, if_true, List.erase_cons_head]
      -- a now holds x's link: the rest of the chain, which a is apart from
      cases xs with
      | nil =>
        simp only [Chain] at hch ⊢
        rw [hch, rd_wr_same]
      | cons y ys =>
        obtain ⟨hy, hy0, hrest⟩ := hch
        refine ⟨by rw [hy, rd_wr_same], hy0, ?_⟩
        apply chain_wr a _ ys y m hrest
        intro z hz
        exact hpa.1 z (List.mem_cons_of_mem x hz)
    · have hc' : c ∈ xs := (List.mem_cons.mp hc).resolve_left fun h => hxc h.symm
      simp only [unlinkM, if_neg hxc]
      rw [show (x :: xs).erase c = x :: xs.erase c by simp [List.erase_cons, hxc]]
      have hrec := ih x m hch (List.pairwise_cons.mp hp).2 hc'
      refine ⟨?_, hx0, hrec⟩
      -- the store lands on a cell of the rest of the chain, apart from a
      rw [unlinkM_rd m c a xs x hpa.1]
      exact hx

end OS4.Pools

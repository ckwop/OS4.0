import OS4.Words.Core
import OS4.Loops
import OS4.Memory
import OS4.FootPrims

/-!
# Reference definitions

The kernel has some hot spots in assembly; `core.fs` keeps their Forth
definitions as the reference. Here the reference words are proven to do
exactly what the model of each primitive does, for every input.
-/

namespace OS4.Refs
open OS4

/-- `fill`'s loop, seen from its last byte. -/
theorem fillM_succ (c : BitVec 8) :
    ∀ (k : Nat) (m : Mem) (a : Cell),
      Prim.fillM (k + 1) m a c = upd (Prim.fillM k m a c) (a + BitVec.ofNat 64 k) c := by
  intro k
  induction k with
  | zero => intro m a; simp [Prim.fillM]
  | succ k ih =>
    intro m a
    show Prim.fillM (k + 1) (upd m a c) (a + 1) c = _
    rw [ih, add_ofNat_succ]
    rfl

/-- One pass of FILL-REF's loop body: store c at a + i, then step i. (The fuel
is written as steps of one, which is how `run` unfolds.) -/
theorem fill_step (n : Nat) (c a i u : Cell) (s r : List Cell) (M : Mem) (p : Cell) (e : Nat) :
    run Words.«fill-ref».code (n + 1 + 1 + 1 + 1 + 1 + 1) 3 ⟨c :: a :: s, i :: u :: r, M, p, e⟩ =
      if i + 1 = u then run Words.«fill-ref».code n 9 ⟨c :: a :: s, r, upd M (a + i) (c.setWidth 8), p, e⟩
      else run Words.«fill-ref».code n 3 ⟨c :: a :: s, (i + 1) :: u :: r, upd M (a + i) (c.setWidth 8), p, e⟩ := by
  simp [forth, wr_one]

/-- The loop from pass k to the end, d + 1 passes later. -/
theorem fill_loop (c a u : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    ∀ (d k n : Nat), k + d + 1 = u.toNat →
      run Words.«fill-ref».code (n + 6 * (d + 1)) 3
          ⟨c :: a :: s, BitVec.ofNat 64 k :: u :: r, Prim.fillM k m a (c.setWidth 8), p, e⟩ =
        run Words.«fill-ref».code n 9 ⟨c :: a :: s, r, Prim.fillM u.toNat m a (c.setWidth 8), p, e⟩ := by
  intro d
  induction d with
  | zero =>
    intro k n hk
    have hk' : k + 1 = u.toNat := by omega
    have hi : BitVec.ofNat 64 k + 1 = u := by bv_omega
    rw [show n + 6 * (0 + 1) = n + 1 + 1 + 1 + 1 + 1 + 1 by omega, fill_step, if_pos hi,
      ← fillM_succ, hk']
  | succ d ih =>
    intro k n hk
    have hi : BitVec.ofNat 64 k + 1 ≠ u := by bv_omega
    have hk1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by bv_omega
    rw [show n + 6 * (d + 1 + 1) = n + 6 * (d + 1) + 1 + 1 + 1 + 1 + 1 + 1 by omega, fill_step,
      if_neg hi, ← fillM_succ, hk1]
    exact ih (k + 1) n (by omega)

/-- FILL-REF does exactly what the FILL primitive does. -/
theorem fill_ref (c u a : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«fill-ref» ⟨c :: u :: a :: s, r, m, p, e⟩ = Prim.fill ⟨c :: u :: a :: s, r, m, p, e⟩ := by
  by_cases h0 : u = 0
  · subst h0
    apply loopThread_eq _ _ 5 _ (by simp [forth, Prim.fillM]) (by simp [forth, outOfFuel])
  · have hN : u.toNat ≠ 0 := by intro h; apply h0; bv_omega
    have start : ∀ x, run Words.«fill-ref».code (x + 1 + 1 + 1) 0 ⟨c :: u :: a :: s, r, m, p, e⟩ =
        run Words.«fill-ref».code x 3
          ⟨c :: a :: s, BitVec.ofNat 64 0 :: u :: r, Prim.fillM 0 m a (c.setWidth 8), p, e⟩ := by
      intro x
      simp only [forth, Prim.fillM, List.getElem?_cons_zero, List.getElem?_cons_succ]
      rw [if_neg h0]
      rfl
    apply loopThread_eq _ _ ((2 + 6 * ((u.toNat - 1) + 1)) + 1 + 1 + 1) _ _ (by simp [forth, outOfFuel])
    rw [start, fill_loop c a u s r m p e (u.toNat - 1) 0 2 (by omega)]
    simp [forth]

/-- FILL-REF writes only the n bytes at addr. Its generated footprint is
"anywhere", as its address is computed in a loop; this one follows from
`fill_ref`, and is what a write through a computed address needs. -/
theorem fill_ref_foot : Foot Words.«fill-ref» 3 0 0 0 [⟨.arg 2 0, .arg 1 0⟩] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, hx with
  | [c, n, a], _ =>
    have h := Prim.fill_foot [c, n, a] zs s r m u e rfl hz
    simp only [List.cons_append, List.nil_append] at h ⊢
    rw [fill_ref]
    exact h

/-! ## CMOVE -/

/-- `cmove`'s loop, seen from its last byte. -/
theorem cmoveM_succ :
    ∀ (k : Nat) (m : Mem) (src dst : Cell),
      Prim.cmoveM (k + 1) m src dst =
        upd (Prim.cmoveM k m src dst) (dst + BitVec.ofNat 64 k) (Prim.cmoveM k m src dst (src + BitVec.ofNat 64 k)) := by
  intro k
  induction k with
  | zero => intro m src dst; simp [Prim.cmoveM]
  | succ k ih =>
    intro m src dst
    show Prim.cmoveM (k + 1) (upd m dst (m src)) (src + 1) (dst + 1) = _
    rw [ih, add_ofNat_succ, add_ofNat_succ]
    rfl

/-- A byte read and stored back: what `c@ c!` moves. -/
theorem byte_move (M : Mem) (a : Cell) : (rd M a 1).setWidth 8 = M a := by
  rw [rd_one]
  exact BitVec.setWidth_setWidth_of_le _ (by omega) |>.trans (BitVec.setWidth_eq _)

/-- One pass of CMOVE-REF's loop body: copy the byte at src + i to dst + i. -/
theorem cmove_step (n : Nat) (dst src i u : Cell) (s r : List Cell) (M : Mem) (p : Cell) (e : Nat) :
    run Words.«cmove-ref».code (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) 2 ⟨dst :: src :: s, i :: u :: r, M, p, e⟩ =
      if i + 1 = u then run Words.«cmove-ref».code n 11 ⟨dst :: src :: s, r, upd M (dst + i) (M (src + i)), p, e⟩
      else run Words.«cmove-ref».code n 2 ⟨dst :: src :: s, (i + 1) :: u :: r, upd M (dst + i) (M (src + i)), p, e⟩ := by
  simp [forth, wr_one, byte_move]

theorem cmove_loop (dst src u : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    ∀ (d k n : Nat), k + d + 1 = u.toNat →
      run Words.«cmove-ref».code (n + 9 * (d + 1)) 2
          ⟨dst :: src :: s, BitVec.ofNat 64 k :: u :: r, Prim.cmoveM k m src dst, p, e⟩ =
        run Words.«cmove-ref».code n 11 ⟨dst :: src :: s, r, Prim.cmoveM u.toNat m src dst, p, e⟩ := by
  intro d
  induction d with
  | zero =>
    intro k n hk
    have hk' : k + 1 = u.toNat := by omega
    have hi : BitVec.ofNat 64 k + 1 = u := by bv_omega
    rw [show n + 9 * (0 + 1) = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, cmove_step, if_pos hi,
      ← cmoveM_succ, hk']
  | succ d ih =>
    intro k n hk
    have hi : BitVec.ofNat 64 k + 1 ≠ u := by bv_omega
    have hk1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by bv_omega
    rw [show n + 9 * (d + 1 + 1) = n + 9 * (d + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, cmove_step,
      if_neg hi, ← cmoveM_succ, hk1]
    exact ih (k + 1) n (by omega)

/-- CMOVE-REF does exactly what the CMOVE primitive does. -/
theorem cmove_ref (u dst src : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«cmove-ref» ⟨u :: dst :: src :: s, r, m, p, e⟩ = Prim.cmove ⟨u :: dst :: src :: s, r, m, p, e⟩ := by
  by_cases h0 : u = 0
  · subst h0
    apply loopThread_eq _ _ 5 _ (by simp [forth, Prim.cmoveM]) (by simp [forth, outOfFuel])
  · have hN : u.toNat ≠ 0 := by intro h; apply h0; bv_omega
    have start : ∀ x, run Words.«cmove-ref».code (x + 1 + 1) 0 ⟨u :: dst :: src :: s, r, m, p, e⟩ =
        run Words.«cmove-ref».code x 2
          ⟨dst :: src :: s, BitVec.ofNat 64 0 :: u :: r, Prim.cmoveM 0 m src dst, p, e⟩ := by
      intro x
      simp only [forth, Prim.cmoveM, List.getElem?_cons_zero, List.getElem?_cons_succ]
      rw [if_neg h0]
      rfl
    apply loopThread_eq _ _ ((2 + 9 * ((u.toNat - 1) + 1)) + 1 + 1) _ _ (by simp [forth, outOfFuel])
    rw [start, cmove_loop dst src u s r m p e (u.toNat - 1) 0 2 (by omega)]
    simp [forth]

/-! ## CMOVE> -/

/-- One pass of CMOVE>-REF's loop: x - 1 more bytes to go, after the byte at x - 1. -/
theorem cmove_up_step (n : Nat) (x dst src : Cell) (s r : List Cell) (M : Mem) (p : Cell) (e : Nat)
    (hx : x ≠ 0) :
    run Words.«cmove>-ref».code (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) 0
        ⟨x :: dst :: src :: s, r, M, p, e⟩ =
      run Words.«cmove>-ref».code n 0
        ⟨(x - 1) :: dst :: src :: s, r, upd M (dst + (x - 1)) (M (src + (x - 1))), p, e⟩ := by
  have hx' : ¬ (x = 0#64) := hx
  simp [forth, wr_one, byte_move, hx']

theorem cmove_up_loop (dst src : Cell) (s r : List Cell) (p : Cell) (e : Nat) :
    ∀ (k : Nat) (M : Mem), k < 2 ^ 64 →
      run Words.«cmove>-ref».code (14 * k + 5) 0 ⟨BitVec.ofNat 64 k :: dst :: src :: s, r, M, p, e⟩ =
        .ok ⟨s, r, Prim.cmoveUpM k M src dst, p, e⟩ := by
  intro k
  induction k with
  | zero => intro M _; simp [forth, Prim.cmoveUpM]
  | succ k ih =>
    intro M hk
    have hx : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      simp at this
      omega
    have hm : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by bv_omega
    rw [show 14 * (k + 1) + 5 = (14 * k + 5) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      cmove_up_step _ _ _ _ _ _ _ _ _ hx, hm, ih _ (by omega)]
    rfl

/-- CMOVE>-REF does exactly what the CMOVE> primitive does. -/
theorem cmove_up_ref (u dst src : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«cmove>-ref» ⟨u :: dst :: src :: s, r, m, p, e⟩ = Prim.cmoveUp ⟨u :: dst :: src :: s, r, m, p, e⟩ := by
  have hu : BitVec.ofNat 64 u.toNat = u := by simp
  apply loopThread_eq _ _ (14 * u.toNat + 5) _ _ (by simp [forth, outOfFuel])
  have h := cmove_up_loop dst src s r p e u.toNat m u.isLt
  rw [hu] at h
  rw [h]
  simp [forth]

/-! ## UM/MOD

UM/MOD-REF keeps the divisor on the return stack, under the loop's
parameters (J), and has no checks: it is compared where the primitive divides
(a divisor that is not 0, a quotient that fits). -/

/-- A round that subtracts: the bit that left was set, or the divisor fits. -/
theorem um_round_sub (n : Nat) (dv hi lo i : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (hc : hi >>> 63 ≠ 0 ∨ ¬ ((hi <<< 1) ||| (lo >>> 63)).ult dv = true) :
    run Words.«um/mod-ref».code (n + 28) 4 ⟨hi :: lo :: s, i :: 64 :: dv :: r, m, p, e⟩ =
      if i + 1 = 64 then
        run Words.«um/mod-ref».code n 32
          ⟨(((hi <<< 1) ||| (lo >>> 63)) - dv) :: ((lo <<< 1) ||| 1) :: s, dv :: r, m, p, e⟩
      else
        run Words.«um/mod-ref».code n 4
          ⟨(((hi <<< 1) ||| (lo >>> 63)) - dv) :: ((lo <<< 1) ||| 1) :: s, (i + 1) :: 64 :: dv :: r, m, p, e⟩ := by
  rw [show n + 28 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  by_cases h0 : hi >>> 63 = 0
  · have hu : ((hi <<< 1) ||| (lo >>> 63)).ult dv = false := by
      rcases hc with hc | hc
      · exact absurd h0 hc
      · simpa using hc
    simp [forth, h0, hu]
  · simp [forth]
    exact fun h => absurd h h0

/-- A round that only shifts. -/
theorem um_round_keep (n : Nat) (dv hi lo i : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (h0 : hi >>> 63 = 0) (hu : ((hi <<< 1) ||| (lo >>> 63)).ult dv = true) :
    run Words.«um/mod-ref».code (n + 22) 4 ⟨hi :: lo :: s, i :: 64 :: dv :: r, m, p, e⟩ =
      if i + 1 = 64 then
        run Words.«um/mod-ref».code n 32 ⟨((hi <<< 1) ||| (lo >>> 63)) :: (lo <<< 1) :: s, dv :: r, m, p, e⟩
      else
        run Words.«um/mod-ref».code n 4
          ⟨((hi <<< 1) ||| (lo >>> 63)) :: (lo <<< 1) :: s, (i + 1) :: 64 :: dv :: r, m, p, e⟩ := by
  rw [show n + 22 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 by omega]
  simp [forth, h0, hu]

/-- The rounds left, from round k. -/
theorem um_loop (dv : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    ∀ (d k : Nat) (hi lo : Cell), k + d + 1 = 64 → ∀ n, ∃ j,
      run Words.«um/mod-ref».code (n + 28 * (d + 1)) 4 ⟨hi :: lo :: s, BitVec.ofNat 64 k :: 64 :: dv :: r, m, p, e⟩ =
        run Words.«um/mod-ref».code (n + j) 32
          ⟨(Prim.umdivRounds dv (d + 1) hi lo).1 :: (Prim.umdivRounds dv (d + 1) hi lo).2 :: s, dv :: r, m, p, e⟩ := by
  intro d
  induction d with
  | zero =>
    intro k hi lo hk n
    have hi64 : BitVec.ofNat 64 k + 1 = 64 := by bv_omega
    by_cases hc : hi >>> 63 ≠ 0 ∨ ¬ ((hi <<< 1) ||| (lo >>> 63)).ult dv = true
    · refine ⟨0, ?_⟩
      rw [show n + 28 * (0 + 1) = n + 28 by omega, um_round_sub n dv hi lo _ s r m p e hc, if_pos hi64]
      simp only [Prim.umdivRounds, if_pos hc, Nat.add_zero]
    · have h0 : hi >>> 63 = 0 := Classical.byContradiction fun h => hc (Or.inl h)
      have hu : ((hi <<< 1) ||| (lo >>> 63)).ult dv = true := Classical.byContradiction fun h => hc (Or.inr h)
      refine ⟨6, ?_⟩
      rw [show n + 28 * (0 + 1) = n + 6 + 22 by omega, um_round_keep (n + 6) dv hi lo _ s r m p e h0 hu,
        if_pos hi64]
      simp only [Prim.umdivRounds, if_neg hc]
  | succ d ih =>
    intro k hi lo hk n
    have hne : BitVec.ofNat 64 k + 1 ≠ 64 := by bv_omega
    have hk1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by bv_omega
    by_cases hc : hi >>> 63 ≠ 0 ∨ ¬ ((hi <<< 1) ||| (lo >>> 63)).ult dv = true
    · obtain ⟨j, hr⟩ := ih (k + 1) _ _ (by omega) n
      refine ⟨j, ?_⟩
      rw [show n + 28 * (d + 1 + 1) = n + 28 * (d + 1) + 28 by omega,
        um_round_sub _ dv hi lo _ s r m p e hc, if_neg hne, hk1, hr]
      simp only [Prim.umdivRounds, if_pos hc]
    · have h0 : hi >>> 63 = 0 := Classical.byContradiction fun h => hc (Or.inl h)
      have hu : ((hi <<< 1) ||| (lo >>> 63)).ult dv = true := Classical.byContradiction fun h => hc (Or.inr h)
      obtain ⟨j, hr⟩ := ih (k + 1) _ _ (by omega) (n + 6)
      refine ⟨6 + j, ?_⟩
      rw [show n + 28 * (d + 1 + 1) = n + 6 + 28 * (d + 1) + 22 by omega,
        um_round_keep _ dv hi lo _ s r m p e h0 hu, if_neg hne, hk1, hr, show n + 6 + j = n + (6 + j) by omega]
      simp only [Prim.umdivRounds, if_neg hc]

/-- UM/MOD-REF does exactly what the UM/MOD primitive does, wherever that
divides. -/
theorem umslashmod_ref (dv hi lo : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (hd : dv ≠ 0) (hlt : hi.ult dv = true) :
    Words.«um/mod-ref» ⟨dv :: hi :: lo :: s, r, m, p, e⟩ = Prim.umslashmod ⟨dv :: hi :: lo :: s, r, m, p, e⟩ := by
  obtain ⟨j, hr⟩ := um_loop dv s r m p e 63 0 hi lo (by omega) 4
  have pre : ∀ n, run Words.«um/mod-ref».code (n + 1 + 1 + 1 + 1) 0 ⟨dv :: hi :: lo :: s, r, m, p, e⟩ =
      run Words.«um/mod-ref».code n 4 ⟨hi :: lo :: s, BitVec.ofNat 64 0 :: 64 :: dv :: r, m, p, e⟩ := by
    intro n
    simp [forth]
  have post : ∀ (n : Nat) (a b : Cell),
      run Words.«um/mod-ref».code (n + 1 + 1 + 1 + 1) 32 ⟨a :: b :: s, dv :: r, m, p, e⟩ =
        .ok ⟨b :: a :: s, r, m, p, e⟩ := by
    intro n a b
    simp [forth]
  have run_all : run Words.«um/mod-ref».code ((4 + 28 * (63 + 1)) + 1 + 1 + 1 + 1) 0
      ⟨dv :: hi :: lo :: s, r, m, p, e⟩ =
      .ok ⟨(Prim.umdivRounds dv (63 + 1) hi lo).2 :: (Prim.umdivRounds dv (63 + 1) hi lo).1 :: s, r, m, p, e⟩ := by
    rw [pre, hr, show 4 + j = j + 1 + 1 + 1 + 1 by omega, post]
  rw [show Words.«um/mod-ref» ⟨dv :: hi :: lo :: s, r, m, p, e⟩ = _ from
    loopThread_eq _ _ _ _ run_all (by simp [outOfFuel])]
  simp only [Prim.umslashmod, if_neg hd, hlt, not_true_eq_false, if_false]

end OS4.Refs

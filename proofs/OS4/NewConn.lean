import OS4.Pools

/-!
# `new-conn` when the free list is empty (V4, H-pool)

`Pools.lean` proves `new-conn`'s step when it recycles a connection from the
free list (`new_conn_pool`). With the free list empty it takes a new record
from `reserve` instead. Here: that path clears the record's header, sets its
retransmission timeout and puts it first on the live list, and keeps `Pool`
(both lists end, their link cells apart), with one more live connection and
the free list as it was (`new_conn_reserve_pool`).

Hypotheses, as for `new_conn_pool`: `reserve` is taken as given (it returns
fresh memory at the top of the dictionary's space, writing only its own
pointer), and the new record's header is apart from the pool's link cells.
-/

namespace OS4.NewConn
open OS4 OS4.Pools

/-- `new-conn`'s memory up to the header, from `reserve`'s memory m1. -/
def reserveM3 (m1 : Mem) (x : Cell) : Mem :=
  wr (Prim.fillM 200 m1 x 0) (x + 112#64) 8 1000#64

/-- Then x first on the live list. -/
def reserveM (m1 : Mem) (x : Cell) : Mem :=
  wr (wr (reserveM3 m1 x) x 8 (rd (reserveM3 m1 x) connsV 8)) connsV 8 x

set_option maxHeartbeats 4000000 in
/-- `new-conn` with the free list empty, and `reserve` giving x. -/
theorem new_conn_reserve_eq (x : Cell) (s r : List Cell) (m m1 : Mem) (u : Cell) (e e1 : Nat)
    (hx : rd m freeV 8 = 0)
    (hrs : Words.«reserve» ⟨12488#64 :: s, r, m, u, e⟩ = .ok ⟨x :: s, r, m1, u, e1⟩) :
    Words.«new-conn» ⟨s, r, m, u, e⟩ = .ok ⟨x :: s, r, reserveM m1 x, u, e1⟩ := by
  rw [show Words.«new-conn» = thread (newConnCode Words.«reserve») from rfl]
  generalize Words.«reserve» = RS at hrs
  simp [forth, newConnCode, reserveM, reserveM3, hx, hrs]

theorem reserveM_rd (m1 : Mem) (x z : Cell) (h2 : Away x z) (h3 : Apart connsV z) :
    rd (reserveM m1 x) z 8 = rd m1 z 8 := by
  unfold reserveM
  rw [rd_wr_other _ _ _ _ h3.2 h3.1, rd_wr_other _ _ _ _ (by obtain ⟨a, b⟩ := h2; bv_omega)
    (by obtain ⟨a, b⟩ := h2; bv_omega)]
  unfold reserveM3
  exact header_rd _ x z h2

/-- **The pool step, from `reserve`:** the new record x joins the live list,
and the free list stays as it was. Assumed: x is not 0, its header is apart
from the pool's link cells and the two list heads, and its own link cell is
apart from them (a record from fresh memory). -/
theorem new_conn_reserve_pool (m1 : Mem) (x : Cell) (L F : List Cell) (hp : Pool m1 L F)
    (hx0 : x ≠ 0)
    (hfar : Away x connsV ∧ Away x freeV ∧ ∀ y ∈ L ++ F, Away x y)
    (hxa : Apart connsV x ∧ Apart freeV x) (hxy : ∀ y ∈ L ++ F, Apart x y) :
    Pool (reserveM m1 x) (x :: L) F := by
  obtain ⟨hl, hf, hh, hlv, hfv, hlp, hfp, hx⟩ := hp
  obtain ⟨hfc, hff, hfy⟩ := hfar
  have keep : ∀ z, Away x z → Apart connsV z → rd (reserveM m1 x) z 8 = rd m1 z 8 :=
    fun z h2 h3 => reserveM_rd m1 x z h2 h3
  refine ⟨?_, ?_, hh, ?_, hfv, ?_, hfp, ?_⟩
  · -- live: x, then the old live list
    refine ⟨?_, hx0, ?_⟩
    · unfold reserveM; exact rd_wr_same _ _ _
    · apply chain_move m1 _ L connsV x
      · unfold reserveM
        rw [rd_wr_other _ _ _ _ hxa.1.2 hxa.1.1, rd_wr_same]
        unfold reserveM3
        exact header_rd _ x connsV hfc
      · intro z hz
        exact keep z (hfy z (List.mem_append_left F hz)) (hlv z hz).1
      · exact hl
  · -- free: as it was
    apply chain_move m1 _ F freeV freeV
    · exact keep freeV hff ⟨hh.1, hh.2⟩
    · intro z hz
      exact keep z (hfy z (List.mem_append_right L hz)) (hfv z hz).1
    · exact hf
  · intro y hy
    rcases List.mem_cons.mp hy with hy1 | hy2
    · rw [hy1]; exact hxa
    · exact hlv y hy2
  · refine List.pairwise_cons.mpr ⟨fun y hy => hxy y (List.mem_append_left F hy), hlp⟩
  · intro a ha b hb
    rcases List.mem_cons.mp ha with ha1 | ha2
    · rw [ha1]; exact hxy b (List.mem_append_right L hb)
    · exact hx a ha2 b hb

end OS4.NewConn

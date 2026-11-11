import OS4.Pools

/-!
# `find-conn` returns a live connection or 0 (V4)

`tcp-in` hands each segment to the connection `find-conn` returns, and
`segment-in` then writes that record. So what it returns must be a live
connection, or 0 for none: a freed record could have been recycled for
another client, or lie on the free list (docs/defects.md, 31, where a stale
hash chain broke exactly this).

`find-conn` walks one hash bucket's chain, through each connection's hash
link (`c.hlink`, 152 bytes in). Here: whatever the segment's addresses and
ports, and whatever the records on the chain hold, the walk ends and returns
0 or a connection on that chain (`find_conn_run`). With the hash table's
invariant, that every connection on a bucket's chain is live (`H ⊆ L`, a
hypothesis here), it returns 0 or a live connection (`find_conn_live`).

Hypotheses, as in `Pools.lean`: `bucket` (a keyed hash, which writes only its
scratch cells) is taken as given, leaving the rx frame, and so `ip-source`,
as they were.
-/

namespace OS4.FindConn
open OS4 OS4.Pools

/-- `find-conn`'s thread, with `ip-source` and `bucket` left as IP and BK. -/
noncomputable def fcCode (IP BK : Sem) : List Ins := [.call IP, .call Words.«i-sport», .call Prim.fetch,
  .call Words.«i-dport», .call Prim.fetch, .call BK, .call Prim.fetch, .call Prim.dup, .zbranch 39,
  .call Prim.dup, .call Words.«c.rport», .call Prim.fetch, .call Words.«i-sport», .call Prim.fetch,
  .call Prim.equal, .call Prim.over, .call Words.«c.lport», .call Prim.fetch, .call Words.«i-dport»,
  .call Prim.fetch, .call Prim.equal, .call Prim.and, .call Prim.over, .call Words.«c.rip», .call Prim.fetch,
  .call IP, .call Prim.equal, .call Prim.and, .call Prim.over, .call Words.«c.state», .call Prim.fetch,
  .call Words.«closed», .call Words.«<>», .call Prim.and, .zbranch 36, .exit, .call Words.«c.hlink»,
  .call Prim.fetch, .branch 7, .exit]

theorem fcCode_eq : Words.«find-conn».code = fcCode Words.«ip-source» Words.«bucket» := rfl

/-- Steps of `find-conn`'s walk from its loop head: 31 a connection it
passes (fewer for the one it returns), 3 at the end of the chain. -/
def fcFuel : List Cell → Nat
  | [] => 3
  | _ :: xs => 31 + fcFuel xs

/-- What the walk tests of connection x: its ports, its address and that it
is not closed, as the flags `and`ed together. -/
def matchC (m : Mem) (x ipv : Cell) : Cell :=
  (((if rd m (x + 32#64) 8 = rd m (wordAddr "i-sport" + 8#64) 8 then 18446744073709551615#64 else 0#64) &&&
    (if rd m (x + 16#64) 8 = rd m (wordAddr "i-dport" + 8#64) 8 then 18446744073709551615#64 else 0#64)) &&&
    (if rd m (x + 24#64) 8 = ipv then 18446744073709551615#64 else 0#64)) &&&
    (if rd m (x + 8#64) 8 = 0#64 then 0#64 else 18446744073709551615#64)

set_option maxHeartbeats 4000000 in
/-- One connection on the chain: the walk returns it, or goes on to the next. -/
theorem find_conn_step (IP BK : Sem) (ipv x : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (k : Nat) (hx0 : x ≠ 0)
    (hip : ∀ s', IP ⟨s', r, m, u, e⟩ = .ok ⟨ipv :: s', r, m, u, e⟩) :
    run (fcCode IP BK) (k + 31) 7 ⟨x :: s, r, m, u, e⟩ =
      if matchC m x ipv = 0#64 then run (fcCode IP BK) k 7 ⟨rd m (x + 152) 8 :: s, r, m, u, e⟩
      else .ok ⟨x :: s, r, m, u, e⟩ := by
  have hx0' : ¬ x = 0#64 := hx0
  rw [show k + 31 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
    + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  simp [forth, fcCode, hx0', hip, matchC]

set_option maxHeartbeats 4000000 in
theorem find_conn_run (IP BK : Sem) (ipv : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hip : ∀ s', IP ⟨s', r, m, u, e⟩ = .ok ⟨ipv :: s', r, m, u, e⟩) :
    ∀ (xs : List Cell) (a : Cell) (n : Nat), HChain m a xs →
      ∃ y, run (fcCode IP BK) (fcFuel xs + n) 7 ⟨rd m a 8 :: s, r, m, u, e⟩ =
        .ok ⟨y :: s, r, m, u, e⟩ ∧ (y = 0 ∨ y ∈ xs) := by
  intro xs
  induction xs with
  | nil =>
    intro a n h
    simp only [HChain] at h
    refine ⟨0, ?_, Or.inl rfl⟩
    simp only [fcFuel]
    rw [show 3 + n = n + 1 + 1 + 1 by omega]
    simp [forth, fcCode, h]
  | cons x xs ih =>
    intro a n h
    obtain ⟨hx, hx0, hc⟩ := h
    obtain ⟨y, hy, hyx⟩ := ih (x + 152) n hc
    simp only [fcFuel]
    rw [show 31 + fcFuel xs + n = (fcFuel xs + n) + 31 by omega, hx]
    rw [find_conn_step IP BK ipv x s r m u e (fcFuel xs + n) hx0 hip]
    by_cases hm0 : matchC m x ipv = 0#64
    · rw [if_pos hm0]
      refine ⟨y, hy, ?_⟩
      rcases hyx with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (List.mem_cons_of_mem x hm)
    · rw [if_neg hm0]
      exact ⟨x, rfl, Or.inr (by simp)⟩

abbrev iSportV : Cell := wordAddr "i-sport" + 8#64
abbrev iDportV : Cell := wordAddr "i-dport" + 8#64

/-- `find-conn` returns 0 or a connection on its bucket's chain; with the
hash table's invariant (each chain's connections are live), 0 or a live one. -/
theorem find_conn_live (ipv b : Cell) (H L s r : List Cell) (m m1 : Mem) (u : Cell) (e e1 : Nat)
    (hip0 : Words.«ip-source» ⟨s, r, m, u, e⟩ = .ok ⟨ipv :: s, r, m, u, e⟩)
    (hb : Words.«bucket» ⟨rd m iDportV 8 :: rd m iSportV 8 :: ipv :: s, r, m, u, e⟩ =
      .ok ⟨b :: s, r, m1, u, e1⟩)
    (hip : ∀ s', Words.«ip-source» ⟨s', r, m1, u, e1⟩ = .ok ⟨ipv :: s', r, m1, u, e1⟩)
    (h : HChain m1 b H) (hHL : ∀ x ∈ H, x ∈ L) :
    ∃ y, Words.«find-conn» ⟨s, r, m, u, e⟩ = .ok ⟨y :: s, r, m1, u, e1⟩ ∧ (y = 0 ∨ y ∈ L) := by
  rw [show Words.«find-conn» = loopThread (fcCode Words.«ip-source» Words.«bucket») from rfl]
  generalize Words.«ip-source» = IP at hip0 hip ⊢
  generalize Words.«bucket» = BK at hb ⊢
  obtain ⟨y, hy, hyH⟩ := find_conn_run IP BK ipv s r m1 u e1 hip H b 0 h
  refine ⟨y, ?_, hyH.elim Or.inl (fun hm => Or.inr (hHL y hm))⟩
  refine loopThread_eq _ _ (fcFuel H + 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ ?_ (by simp [outOfFuel])
  simp [run, fcCode, hip0, hb, Prim.fetch, forth]
  simpa [fcCode, forth] using hy

end OS4.FindConn

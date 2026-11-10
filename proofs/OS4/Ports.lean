import OS4.Words.NetUdp
import OS4.Words.NetTcp

/-!
# Port 0 and released connections (V4)

A free slot in the UDP port table, and in the TCP listeners' table, holds
port 0. So a lookup of port 0 by the slot search alone finds a free slot: a
datagram to UDP port 0 ran whatever handler that slot had held, or xt 0, and
a SYN to TCP port 0 was answered and its connection queued where nothing
accepts it (docs/defects.md, 26 and 27; DECISIONS.md #140). `udp-find` and
`listener-of` now answer 0 for port 0 without searching (`udp_find_zero`,
`listener_of_zero`), and pass any other port to the search unchanged; `udp-in`
executes a handler only when `udp-find` returns a slot, and `tcp-in` treats a
SYN as for a listener only when `listener-of` does.

`release-conn` leaves a connection that is already closed alone
(`release_conn_closed`): its stack loses the connection and nothing else
changes. `close-connection` frees a closed connection itself, so a second
release (the timer sweep's, after a throw) can no longer free it twice
(defect 30). Part of H-pool: every path frees a live connection exactly once.
-/

namespace OS4.Ports
open OS4

/-- A call's outcome, passed on as it is. -/
def pass : Except Fail S → Except Fail S
  | .ok st => .ok st
  | .error x => .error x

/-- `udp-find` gives 0 for port 0, touching nothing. -/
theorem udp_find_zero (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«udp-find» ⟨0 :: s, r, m, p, e⟩ = .ok ⟨0 :: s, r, m, p, e⟩ := by
  simp only [Words.«udp-find», Words.«udp-find».code]
  generalize Words.«udp-slot-of» = U
  simp [forth]

/-- Any other port goes to the slot search as it is. -/
theorem udp_find_ne (port : Cell) (h : port ≠ 0) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«udp-find» ⟨port :: s, r, m, p, e⟩ = pass (Words.«udp-slot-of» ⟨port :: s, r, m, p, e⟩) := by
  simp only [Words.«udp-find», Words.«udp-find».code]
  generalize Words.«udp-slot-of» = U
  simp [forth, h, pass]
  cases U ⟨port :: s, r, m, p, e⟩ <;> rfl

/-- `listener-of` gives 0 for port 0, touching nothing. -/
theorem listener_of_zero (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«listener-of» ⟨0 :: s, r, m, p, e⟩ = .ok ⟨0 :: s, r, m, p, e⟩ := by
  simp only [Words.«listener-of», Words.«listener-of».code]
  generalize Words.«port-slot» = P
  simp [forth]

/-- Any other port goes to the slot search as it is. -/
theorem listener_of_ne (port : Cell) (h : port ≠ 0) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    Words.«listener-of» ⟨port :: s, r, m, p, e⟩ = pass (Words.«port-slot» ⟨port :: s, r, m, p, e⟩) := by
  simp only [Words.«listener-of», Words.«listener-of».code]
  generalize Words.«port-slot» = P
  simp [forth, h, pass]
  cases P ⟨port :: s, r, m, p, e⟩ <;> rfl

/-- A connection already closed (state 0, the cell 8 bytes in) is left
alone: no store, no wake, no free. -/
theorem release_conn_closed (conn : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (h : rd m (conn + 8#64) 8 = 0) :
    Words.«release-conn» ⟨conn :: s, r, m, p, e⟩ = .ok ⟨s, r, m, p, e⟩ := by
  simp only [Words.«release-conn», Words.«release-conn».code]
  generalize Words.«wake-owner» = W
  generalize Words.«free-conn» = F
  generalize Words.«flag+» = FP
  generalize Words.«flag?» = FQ
  simp [forth, h]

end OS4.Ports

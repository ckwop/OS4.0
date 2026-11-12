import OS4.Words.NetNet
import OS4.Memory

/-!
# The parsers' front (V4)

What the network stack reads of a frame before it trusts it. `frame-in`
looks only at the frame's length and its two type bytes, and only when the
frame holds them; it hands ARP and IPv4 packets on with the length that is
left, and drops everything else.
-/

namespace OS4.Parsers
open OS4

/-- The frame being handled, and the counter `frame-in` bumps. -/
abbrev rxFrame : Cell := dictTop - 12424
abbrev framesIn : Cell := wordAddr "frames-in" + 8

/-- A handler's outcome, passed on as it is (the thread's call of it). -/
def pass : Except Fail S → Except Fail S
  | .ok st => .ok st
  | .error x => .error x

set_option maxHeartbeats 4000000 in
/-- `frame-in`, for any frame: below 14 bytes it is dropped; otherwise the
type at bytes 12 and 13 (the only bytes it reads) chooses ARP, IPv4 or
nothing, and the handler gets the rest of the frame. -/
theorem frame_in_dispatch (len : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    let mf := wr m framesIn 8 (rd m framesIn 8 + 1)
    let ty := rd mf (rxFrame + 12) 1 <<< 8 ||| rd mf (rxFrame + 12 + 1) 1
    Words.«frame-in» ⟨len :: s, r, m, p, e⟩ =
      if len.slt 14 then .ok ⟨s, r, mf, p, e⟩
      else if ty = 2054 then pass (Words.«arp-in» ⟨(len - 14) :: (rxFrame + 14) :: s, r, mf, p, e⟩)
      else if ty = 2048 then pass (Words.«ip-in» ⟨(len - 14) :: s, r, mf, p, e⟩)
      else .ok ⟨s, r, mf, p, e⟩ := by
  intro mf ty
  simp only [Words.«frame-in», Words.«frame-in».code]
  generalize ha : Words.«arp-in» = AI
  generalize hi : Words.«ip-in» = II
  simp [forth, mf, ty, rxFrame, framesIn, pass]
  cases BitVec.slt len 14#64 <;> simp <;> rfl

end OS4.Parsers

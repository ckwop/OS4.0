import OS4.Words.NetIcmp
import OS4.IpCheck

/-!
# What an ICMP report quotes (V4)

"Destination unreachable" tells a sender its packet could not be delivered,
quoting the packet's header and first 8 bytes of payload. A packet may have
fewer: `ip-check` allows any total from the header's length up, and past the
packet's end `rx-frame` still holds an earlier frame's bytes, someone else's.
So `(unreachable)` quotes the header and 8 bytes or the whole packet,
whichever is shorter (DECISIONS.md #138): `unreachable_quote` shows that is
the count its CMOVE gets, from the packet's start, and `quote_le` that it
never passes the packet's own total length, nor 68 bytes. With
`ip_check_bounds` (total ≤ len), what is quoted lies inside the frame as
received.
-/

namespace OS4.Parsers
open OS4

/-- Where the quote goes: after the report's 8-byte header in tx-frame. -/
abbrev txQuote : Cell := dictTop - 14472#64 + 34#64 + 8#64

/-- How much of the packet a report quotes: its header and 8 bytes, or the
whole packet if that is shorter. -/
abbrev quoteLen (m : Mem) : Cell :=
  if BitVec.slt (n16 m (rxIp + 2#64)) (ihlOf m + 8#64) then n16 m (rxIp + 2#64) else ihlOf m + 8#64

set_option maxHeartbeats 4000000 in
/-- From reading the header length to the copy: CMOVE takes `quoteLen`
bytes from the packet's start, whatever the memory holds. -/
theorem unreachable_quote (k : Nat) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«(unreachable)».code (k + 22) 23 ⟨s, r, m, p, e⟩ =
      run Words.«(unreachable)».code k 45 ⟨quoteLen m :: txQuote :: rxIp :: s, quoteLen m :: r, m, p, e⟩ := by
  rw [show k + 22 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
    by omega]
  simp only [Words.«(unreachable)».code, quoteLen, n16]
  generalize Words.«icmp-send» = IS
  generalize Words.«ip-source» = SRC
  by_cases h : BitVec.slt (rd m (rxIp + 2#64) 1 <<< 8 ||| rd m (rxIp + 2#64 + 1#64) 1) (ihlOf m + 8#64) <;>
  simp_all [forth] <;> rfl

theorem code_45 : Words.«(unreachable)».code[45]? = some (.call Prim.cmove) := rfl

theorem n16_lt (b0 b1 : BitVec 8) : (b0.setWidth 64 <<< 8 ||| b1.setWidth 64 : Cell) < 65536#64 := by
  bv_decide

theorem ihl_le (v : BitVec 8) : (v.setWidth 64 &&& 15#64) * 4#64 ≤ (60#64 : Cell) := by bv_decide

theorem min_le (t a : Cell) (ht : t < 65536#64) (ha : a ≤ 60#64) :
    (if BitVec.slt t (a + 8#64) then t else a + 8#64) ≤ t ∧
    (if BitVec.slt t (a + 8#64) then t else a + 8#64) ≤ 68#64 := by
  split <;> bv_decide

/-- The quote never passes the packet's total length, nor 68 bytes. -/
theorem quote_le (m : Mem) : quoteLen m ≤ n16 m (rxIp + 2#64) ∧ quoteLen m ≤ 68#64 := by
  simp only [quoteLen, n16, ihlOf, rd_one]
  exact min_le _ _ (n16_lt _ _) (ihl_le _)

end OS4.Parsers

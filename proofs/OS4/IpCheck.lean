import OS4.Words.NetIp
import OS4.Words.NetUdp
import OS4.Specs.NetEth

/-!
# What IP accepts (V4)

`ip-check` passes a packet on only when its header length (ihl) is at least
20 and within the frame's length, and its total length lies between the two:
20 ≤ ihl ≤ total ≤ len. So the payload `ip-in` hands on, `total - ihl` bytes
at `ihl`, lies inside the frame as received, whatever the header claims.
-/

namespace OS4.Parsers
open OS4

/-- The packet: rx-frame after its Ethernet header. -/
abbrev rxIp : Cell := dictTop - 12160#64 + 14#64
/-- Its header length, from the first byte. -/
abbrev ihlOf (m : Mem) : Cell := (rd m rxIp 1 &&& 15#64) * 4#64

set_option maxHeartbeats 4000000 in
/-- The version and the header length, before the checksum. -/
theorem ip_check_head (k : Nat) (len : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«ip-check».code (k + 24) 0 ⟨len :: s, r, m, p, e⟩ =
      if rd m rxIp 1 >>> 4 = 4#64 ∧ BitVec.slt len (ihlOf m) = false ∧ BitVec.slt (ihlOf m) 20#64 = false
      then run Words.«ip-check».code (k + 3) 27 ⟨ihlOf m :: len :: s, r, m, p, e⟩
      else .ok ⟨0#64 :: s, r, m, p, e⟩ := by
  rw [show k + 24 = k + 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
    by omega]
  simp only [Words.«ip-check».code]
  generalize Words.«checksum» = CK
  by_cases h1 : rd m rxIp 1 >>> 4 = 4#64 <;>
  by_cases h2 : BitVec.slt len (ihlOf m) = false <;>
  by_cases h3 : BitVec.slt (ihlOf m) 20#64 = false <;>
  simp_all [forth]

set_option maxHeartbeats 4000000 in
/-- The checksum: whatever it reads, it leaves the two lengths, and decides. -/
theorem ip_check_sum (k : Nat) (ihl len : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    (∃ x, run Words.«ip-check».code (k + 7) 27 ⟨ihl :: len :: s, r, m, p, e⟩ = .error x) ∨
    ∃ f m2 e2, run Words.«ip-check».code (k + 7) 27 ⟨ihl :: len :: s, r, m, p, e⟩ =
      if f = 0#64 then run Words.«ip-check».code (k + 3) 34 ⟨ihl :: len :: s, r, m2, p, e2⟩
      else .ok ⟨0#64 :: s, r, m2, p, e2⟩ := by
  have hs := Words.«checksum».spec [ihl, dictTop - 12160#64 + 14#64] [] (ihl :: len :: s) r m p e rfl rfl
  simp only [List.cons_append, List.nil_append] at hs
  rw [show k + 7 = k + 3 + 1 + 1 + 1 + 1 by omega]
  cases hck : Words.«checksum» ⟨ihl :: (dictTop - 12160#64 + 14#64) :: ihl :: len :: s, r, m, p, e⟩ with
  | error x =>
    left
    refine ⟨x, ?_⟩
    simp only [Words.«ip-check».code]
    generalize Words.«checksum» = CK at hck ⊢
    simp [forth, hck]
  | ok st2 =>
    rw [hck] at hs
    obtain ⟨⟨ys, hy, hds⟩, ⟨ws, hw, hrs⟩, hup⟩ := hs
    obtain ⟨ds2, rs2, m2, u2, e2⟩ := st2
    simp only at hds hrs hup
    match ys, ws, hy, hw with
    | [f], [], _, _ =>
      right
      refine ⟨f, m2, e2, ?_⟩
      simp only [List.cons_append, List.nil_append] at hds hrs
      subst hds hrs hup
      simp only [Words.«ip-check».code]
      generalize Words.«checksum» = CK at hck ⊢
      by_cases hf : f = 0#64 <;> simp [forth, hck, hf]

/-- A big-endian 16-bit field, as `n16@` reads it. -/
abbrev n16 (m : Mem) (a : Cell) : Cell := rd m a 1 <<< 8 ||| rd m (a + 1) 1

set_option maxHeartbeats 4000000 in
/-- The total length: within the frame, and at least the header. -/
theorem ip_check_total (k : Nat) (ihl len : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«ip-check».code (k + 14) 34 ⟨ihl :: len :: s, r, m, p, e⟩ =
      if BitVec.slt len (n16 m (rxIp + 2#64)) = false ∧ BitVec.slt (n16 m (rxIp + 2#64)) ihl = false
      then run Words.«ip-check».code (k + 3) 51 ⟨n16 m (rxIp + 2#64) :: ihl :: s, r, m, p, e⟩
      else .ok ⟨0#64 :: s, r, m, p, e⟩ := by
  rw [show k + 14 = k + 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  simp only [Words.«ip-check».code]
  generalize Words.«checksum» = CK
  simp only [n16, rxIp]
  generalize ht : rd m (dictTop - 12160#64 + 14#64 + 2#64) 1 <<< 8 |||
    rd m (dictTop - 12160#64 + 14#64 + 2#64 + 1#64) 1 = t
  by_cases h1 : BitVec.slt len t = false <;>
  by_cases h2 : BitVec.slt t ihl = false <;>
  simp_all [forth]

set_option maxHeartbeats 4000000 in
/-- The rest (fragments, the destination, the source) only decide. -/
theorem ip_check_tail (k : Nat) (t ihl : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (st' : S) (h : run Words.«ip-check».code (k + 30) 51 ⟨t :: ihl :: s, r, m, p, e⟩ = .ok st') :
    st'.ds = 0#64 :: s ∨ st'.ds = 18446744073709551615#64 :: t :: ihl :: s := by
  rw [show k + 30 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega] at h
  simp only [Words.«ip-check».code] at h
  generalize Words.«checksum» = CK at h
  simp [forth] at h
  repeat' split at h
  all_goals (first | (cases h; simp) | simp_all)

/-- What `ip-check` accepts: either it says no (0), or it leaves the header
length and the total length with 20 ≤ ihl ≤ total ≤ len (as signed cells,
the comparisons the code makes). -/
theorem ip_check_bounds (len : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) (st' : S)
    (h : Words.«ip-check» ⟨len :: s, r, m, p, e⟩ = .ok st') :
    st'.ds = 0#64 :: s ∨ ∃ ihl total, st'.ds = 18446744073709551615#64 :: total :: ihl :: s ∧
      BitVec.slt ihl 20#64 = false ∧ BitVec.slt len ihl = false ∧
      BitVec.slt len total = false ∧ BitVec.slt total ihl = false := by
  simp only [Words.«ip-check», thread] at h
  rw [show Words.«ip-check».code.length = 62 + 24 from rfl, ip_check_head 62] at h
  split at h
  · rename_i hc
    obtain ⟨_, h2, h3⟩ := hc
    rw [show 62 + 3 = 58 + 7 from rfl] at h
    rcases ip_check_sum 58 (ihlOf m) len s r m p e with ⟨x, hx⟩ | ⟨f, m2, e2, hf⟩
    · rw [hx] at h; cases h
    · rw [hf] at h
      split at h
      · rw [show 58 + 3 = 47 + 14 from rfl, ip_check_total] at h
        split at h
        · rename_i hc2
          obtain ⟨h4, h5⟩ := hc2
          rw [show 47 + 3 = 20 + 30 from rfl] at h
          rcases ip_check_tail 20 _ _ s r m2 p e2 st' h with h6 | h6
          · exact Or.inl h6
          · exact Or.inr ⟨_, _, h6, h3, h2, h4, h5⟩
        · simp only [Except.ok.injEq] at h; subst h; simp
      · simp only [Except.ok.injEq] at h; subst h; simp
  · simp only [Except.ok.injEq] at h; subst h; simp

set_option maxHeartbeats 4000000 in
/-- UDP likewise: `udp-in` goes past its length check only when the
datagram's length field (ul) is at least its 8-byte header and within the
IP payload: 8 ≤ ul ≤ len. From there on it works with ul, not the IP
length, so the data it hands a port's handler (`ul - 8` bytes after the
header) lies inside the payload. -/
theorem udp_in_head (k : Nat) (len seg : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«udp-in».code (k + 19) 0 ⟨len :: seg :: s, r, m, p, e⟩ =
      if BitVec.slt (n16 (wr m (wordAddr "rx-udp" + 8#64) 8 seg) (seg + 4#64)) 8#64 = false ∧
         BitVec.slt len (n16 (wr m (wordAddr "rx-udp" + 8#64) 8 seg) (seg + 4#64)) = false
      then run Words.«udp-in».code (k + 2) 20
        ⟨n16 (wr m (wordAddr "rx-udp" + 8#64) 8 seg) (seg + 4#64) :: seg :: s, r,
          wr m (wordAddr "rx-udp" + 8#64) 8 seg, p, e⟩
      else .ok ⟨s, r, wr m (wordAddr "rx-udp" + 8#64) 8 seg, p, e⟩ := by
  rw [show k + 19 = k + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  simp only [Words.«udp-in».code, n16]
  generalize Words.«sum16» = S16
  generalize Words.«fold» = FD
  generalize ht : rd (wr m (wordAddr "rx-udp" + 8#64) 8 seg) (seg + 4#64) 1 <<< 8 |||
    rd (wr m (wordAddr "rx-udp" + 8#64) 8 seg) (seg + 4#64 + 1#64) 1 = t
  by_cases h1 : BitVec.slt t 8#64 = false <;>
  by_cases h2 : BitVec.slt len t = false <;>
  simp_all [forth]

end OS4.Parsers

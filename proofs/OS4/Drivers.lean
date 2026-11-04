import OS4.Words.HalVirtioNet
import OS4.FootPrims

/-!
# The network card's driver (V4)

The bare-metal driver (`hal/virtio-net.fs`), as compiled: the device writes
the used ring, so the buffer id and the length `vq-take` reads are anything
at all. Here `net-poll`'s copy is shown safe whatever they are: an id the
driver never posted gives 0 and changes nothing; any other copies at most
2036 bytes, the frame without its virtio header, into the caller's buffer
and nowhere else. `net-send` likewise copies at most 2036 bytes, whatever
length its caller asks for, into its own transmit buffer and nowhere else.

What is left (V4): the stores into the rings and registers (`desc!`,
`vq-submit`, `vm!`), whose addresses come from each queue's record, so
bounding them needs an invariant that the record still holds the addresses
`new-vq` gave it.
-/

namespace OS4.Drivers
open OS4

/-- The length the driver copies: the device's (or the caller's), held to 0
to 2036 as the code's `0 max ... min` does. -/
def clamp (x : Cell) : Cell :=
  if x.slt 0#64 then 0#64 else if (2036#64).slt x then 2036#64 else x

theorem clamp_le (x : Cell) : (clamp x).toNat ≤ 2036 := by
  have : clamp x ≤ 2036#64 := by unfold clamp; split <;> (try split) <;> bv_decide
  simpa [BitVec.le_def] using this

set_option maxHeartbeats 4000000 in
/-- From the length check on: whatever id and length the device reported. -/
theorem net_poll_copy (k : Nat) (len id addr : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    (id.ult 64#64 = false →
      run Words.«net-poll».code (k + 21) 15 ⟨len :: id :: addr :: s, r, m, p, e⟩ = .ok ⟨0 :: s, r, m, p, e⟩) ∧
    (id.ult 64#64 = true →
      run Words.«net-poll».code (k + 21) 15 ⟨len :: id :: addr :: s, r, m, p, e⟩ =
        run Words.«net-poll».code k 40
          ⟨id :: s, clamp (len - 12) :: r,
            Prim.cmoveM (clamp (len - 12)).toNat m (id * 2048 + (wordAddr "rx-bufs" + 8) + 12) addr,
            p, e⟩) := by
  rw [show k + 21 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 by omega]
  refine ⟨fun hid => ?_, fun hid => ?_⟩
  · simp [forth, hid]
  · unfold clamp
    cases h1 : (len - 12#64).slt 0#64 <;> cases h2 : (2036#64).slt (len - 12#64) <;>
      simp [forth, hid, h1, h2] <;> rfl

/-- So the copy writes the caller's buffer, and nothing else. -/
theorem net_poll_copy_bounded (n : Cell) (hn : n.toNat ≤ 2036) (m : Mem) (src addr x : Cell)
    (hx : 2036 ≤ (x - addr).toNat) : Prim.cmoveM n.toNat m src addr x = m x :=
  cmoveM_other x _ m src addr fun j hj hxa => by subst hxa; bv_omega

set_option maxHeartbeats 4000000 in
/-- `net-send`, from the length check to the copy: whatever length the caller
asks for, at most 2036 bytes are copied, into `tx-buf` after its header; an
empty frame is not sent at all (defect 23). -/
theorem net_send_copy (k : Nat) (len addr : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    run Words.«net-send».code (k + 19) 5 ⟨len :: addr :: s, r, m, p, e⟩ =
      if clamp len = 0 then .ok ⟨s, r, m, p, e⟩
      else run Words.«net-send».code k 26 ⟨s, clamp len :: r,
        Prim.cmoveM (clamp len).toNat (Prim.fillM 12 m (wordAddr "tx-buf" + 8) 0) addr
          (wordAddr "tx-buf" + 8 + 12), p, e⟩ := by
  rw [show k + 19 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  unfold clamp
  cases h1 : len.slt 0#64 <;> cases h2 : (2036#64).slt len <;> by_cases h0 : len = 0#64 <;>
    simp [forth, h1, h2, h0] <;> (try rfl) <;> (subst h0; simp at h1 h2)

/-- So the header and the copy write the 2048 bytes of `tx-buf`, and nothing
else. -/
theorem net_send_copy_bounded (n : Cell) (hn : n.toNat ≤ 2036) (m : Mem) (addr x : Cell)
    (hx : 2048 ≤ (x - (wordAddr "tx-buf" + 8)).toNat) :
    Prim.cmoveM n.toNat (Prim.fillM 12 m (wordAddr "tx-buf" + 8) 0) addr
      (wordAddr "tx-buf" + 8 + 12) x = m x := by
  rw [cmoveM_other x _ _ addr _ fun j hj hxa => by subst hxa; bv_omega]
  exact fillM_other x _ m _ 0 fun j hj hxa => by subst hxa; bv_omega

end OS4.Drivers

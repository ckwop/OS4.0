import OS4.Words.HalVirtioNet
import OS4.Words.HalVirtioBlk
import OS4.FootPrims
import OS4.Memory

/-!
# The network card's driver (V4)

The bare-metal driver (`hal/virtio-net.fs`), as compiled: the device writes
the used ring, so the buffer id and the length `vq-take` reads are anything
at all. Here `net-poll`'s copy is shown safe whatever they are: an id the
driver never posted gives 0 and changes nothing; any other copies at most
2036 bytes, the frame without its virtio header, into the caller's buffer
and nowhere else. `net-send` likewise copies at most 2036 bytes, whatever
length its caller asks for, into its own transmit buffer and nowhere else.

The stores into the rings (`desc!`, `vq-submit`) take their addresses from
each queue's record, so they are bounded under an invariant on it (`RxQueue`:
what `new-vq` set). Under it, `rx-post`, which hands a buffer back after
every frame, writes only the receive queue's descriptor table, its available
ring and the card's notify register, whatever index the ring holds.
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

/-! ## The rings

The stores into a queue's rings take their addresses from the queue's record
(size, descriptor table, available ring), so what they write is bounded only
while the record holds what `new-vq` put there. -/

/-- A store of w bytes at a, wholly apart from the cell at b, leaves it alone. -/
theorem rd_wr_apart (m : Mem) (a b v : Cell) (w : Nat) (h1 : w ≤ (b - a).toNat) (h2 : 8 ≤ (a - b).toNat) :
    rd (wr m a w v) b 8 = rd m b 8 := by
  apply rd_congr
  intro i hi
  apply wr_apply_other
  intro j hj heq
  have hi' : (BitVec.ofNat 64 i).toNat = i := by simp; omega
  have hj' : (BitVec.ofNat 64 j).toNat = j := by simp; omega
  bv_omega

/-- A ring index masked by size - 1 is below the size. -/
theorem and_mask_le (x sz : Cell) (h : 1 ≤ sz.toNat) : (x &&& (sz - 1)).toNat ≤ sz.toNat - 1 := by
  rw [BitVec.toNat_and]
  have : (sz - 1).toNat = sz.toNat - 1 := by bv_omega
  rw [← this]
  exact Nat.and_le_right

theorem ofNat_small (j k : Nat) (h : j < k) (hk : k ≤ 8) : (BitVec.ofNat 64 j).toNat = j := by
  simp; omega

set_option maxHeartbeats 4000000 in
/-- `vq-submit` writes the available ring (its index and one entry, masked
into range) and the device's notify register, and nothing else: whatever
index the ring holds, given the record's size and ring address, and a ring
apart from the record. -/
theorem vq_submit_frame (head vq base n : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (sz av : Cell) (hsz : rd m vq 8 = sz) (h1 : 1 ≤ sz.toNat) (h2 : sz.toNat ≤ 32768)
    (hav : rd m (vq + 24#64) 8 = av)
    (hsep1 : 2 * sz.toNat + 4 ≤ (vq + 24#64 - av).toNat) (hsep2 : 8 ≤ (av - (vq + 24#64)).toNat) :
    ∃ m', Words.«vq-submit» ⟨n :: base :: vq :: head :: s, r, m, p, e⟩ = .ok ⟨s, r, m', p, e⟩ ∧
      ∀ x : Cell, 2 * sz.toNat + 4 ≤ (x - av).toNat → 4 ≤ (x - (base + 80#64)).toNat → m' x = m x := by
  simp [forth, hav, hsz]
  intro x hx hb
  generalize hi : (rd m (av + 2#64) 2 &&& sz - 1#64) = i
  have hile : i.toNat ≤ sz.toNat - 1 := hi ▸ and_mask_le _ _ h1
  have hsh : i <<< 1 = i * 2#64 := by bv_decide
  rw [hsh, rd_wr_apart m (i * 2#64 + 4#64 + av) (vq + 24#64) head 2 (by bv_omega) (by bv_omega), hav]
  rw [wr_apply_other x 4 _ (base + 80#64) n (fun j hj h => by
        have := ofNat_small j 4 hj (by omega); bv_omega),
      wr_apply_other x 2 _ (av + 2#64) _ (fun j hj h => by
        have := ofNat_small j 2 hj (by omega); bv_omega),
      wr_apply_other x 2 _ _ head (fun j hj h => by
        have := ofNat_small j 2 hj (by omega); bv_omega)]

set_option maxHeartbeats 4000000 in
/-- `desc!` writes descriptor i, 16 bytes into the table the record names. -/
theorem desc_store_frame (addr len flags next vq i : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (D : Cell) (hD : rd m (vq + 16#64) 8 = D) :
    ∃ m', Words.«desc!» ⟨i :: vq :: next :: flags :: len :: addr :: s, r, m, p, e⟩ = .ok ⟨s, r, m', p, e⟩ ∧
      ∀ x : Cell, 16 ≤ (x - (D + i * 16#64)).toNat → m' x = m x := by
  simp [forth, hD]
  intro x hx
  rw [wr_apply_other x 8 _ _ _ (fun j hj h => by have := ofNat_small j 8 hj (by omega); bv_omega),
    wr_apply_other x 4 _ _ _ (fun j hj h => by have := ofNat_small j 4 hj (by omega); bv_omega),
    wr_apply_other x 2 _ _ _ (fun j hj h => by have := ofNat_small j 2 hj (by omega); bv_omega),
    wr_apply_other x 2 _ _ _ (fun j hj h => by have := ofNat_small j 2 hj (by omega); bv_omega)]

/-- Descriptor `id` of a 64-entry table at D lies within it. -/
theorem entry_in (x D id : Cell) (hid : id.toNat < 64) (hx : 1024 ≤ (x - D).toNat) :
    16 ≤ (x - (D + id * 16#64)).toNat := by
  bv_omega

/-- A byte of the queue's record (40 bytes) is not in its descriptor table. -/
theorem record_apart (Q D id c : Cell) (hc : c.toNat < 40) (hid : id.toNat < 64)
    (h1 : 40 ≤ (D - Q).toNat) (h2 : 1024 ≤ (Q - D).toNat) :
    16 ≤ (Q + c - (D + id * 16#64)).toNat := by
  bv_omega

theorem avail_cell (i : Nat) (hi : i < 8) : (24#64 + BitVec.ofNat 64 i).toNat < 40 := by
  have := ofNat_small i 8 hi (by omega)
  bv_omega

/-- The receive queue's record as `new-vq` leaves it: 64 entries, the
descriptor table just after the 40-byte record (aligned to 16), and the
available ring just after the table. Nothing writes the record afterwards. -/
structure RxQueue (m : Mem) (D AV : Cell) : Prop where
  size : rd m (wordAddr "#rx-bufs" + 16#64) 8 = 64#64
  desc : rd m (wordAddr "#rx-bufs" + 16#64 + 16#64) 8 = D
  avail : rd m (wordAddr "#rx-bufs" + 16#64 + 24#64) 8 = AV
  gap : 40 ≤ (D - (wordAddr "#rx-bufs" + 16#64)).toNat ∧ (D - (wordAddr "#rx-bufs" + 16#64)).toNat ≤ 55
  after : AV = D + 1024#64

set_option maxHeartbeats 400000 in
/-- `rx-post`, giving buffer `id` back to the card (as `net-poll` does after
every frame, with the id it checked is below 64): it writes only the receive
queue's descriptor table and available ring, and the card's notify
register. -/
theorem rx_post_frame (id : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) (D AV : Cell)
    (hq : RxQueue m D AV) (hid : id.toNat < 64) :
    ∃ m' b, Words.«rx-post» ⟨id :: s, r, m, p, e⟩ = .ok ⟨s, r, m', p, e⟩ ∧
      ∀ x : Cell, 1024 ≤ (x - D).toNat → 132 ≤ (x - AV).toNat → 4 ≤ (x - (b + 80#64)).toNat →
        m' x = m x := by
  obtain ⟨hsz, hD, hAV, ⟨g1, g2⟩, hAD⟩ := hq
  generalize hQ : wordAddr "#rx-bufs" + 16#64 = Q at hsz hD hAV g1 g2
  have hsepD2 : 1024 ≤ (Q - D).toNat := by bv_omega
  have hsep1 : 132 ≤ (Q + 24#64 - AV).toNat := by subst hAD; bv_omega
  have hsep2 : 8 ≤ (AV - (Q + 24#64)).toNat := by subst hAD; bv_omega
  obtain ⟨m1, h1, f1⟩ := desc_store_frame (id * 2048#64 + (wordAddr "rx-bufs" + 8#64)) 2048#64 2#64 0#64
    Q id (id :: s) r m p e D hD
  have e1 : rd m1 Q 8 = 64#64 := by
    rw [← hsz]; apply rd_congr; intro i hi; apply f1
    have := ofNat_small i 8 hi (by omega)
    exact record_apart Q D id _ (by omega) hid g1 hsepD2
  have e2 : rd m1 (Q + 24#64) 8 = AV := by
    rw [← hAV]; apply rd_congr; intro i hi; apply f1
    have := ofNat_small i 8 hi (by omega)
    rw [BitVec.add_assoc]
    exact record_apart Q D id _ (avail_cell i hi) hid g1 hsepD2
  have hs1 : 2 * (64#64).toNat + 4 ≤ (Q + 24#64 - AV).toNat := by simpa using hsep1
  obtain ⟨m2, h2, f2⟩ := vq_submit_frame id Q (rd m1 (wordAddr "net-base" + 8#64) 8) 0#64 s r m1 p e
    64#64 AV e1 (by decide) (by decide) e2 hs1 hsep2
  refine ⟨m2, rd m1 (wordAddr "net-base" + 8#64) 8, ?_, ?_⟩
  · simp only [Words.«rx-post», Words.«rx-post».code]
    generalize hd : Words.«desc!» = DS at h1 ⊢
    generalize hv : Words.«vq-submit» = VS at h2 ⊢
    simp [forth]
    rw [hQ, h1]
    dsimp only
    rw [h2]
  · intro x hx1 hx2 hx3
    have hx2' : 2 * (64#64).toNat + 4 ≤ (x - AV).toNat := by simpa using hx2
    rw [f2 x hx2' hx3, f1 x (entry_in x D id hid hx1)]

/-- The transmit queue's record as `new-vq` leaves it: 8 entries, laid out
like the receive queue's. -/
structure TxQueue (m : Mem) (D AV : Cell) : Prop where
  size : rd m (wordAddr "rx-vq" + 16#64) 8 = 8#64
  desc : rd m (wordAddr "rx-vq" + 16#64 + 16#64) 8 = D
  avail : rd m (wordAddr "rx-vq" + 16#64 + 24#64) 8 = AV
  gap : 40 ≤ (D - (wordAddr "rx-vq" + 16#64)).toNat ∧ (D - (wordAddr "rx-vq" + 16#64)).toNat ≤ 55
  after : AV = D + 128#64

/-- A byte of an 8-entry queue's record is not in descriptor 0. -/
theorem record_apart0 (Q D c : Cell) (hc : c.toNat < 40) (h1 : 40 ≤ (D - Q).toNat) (h2 : 128 ≤ (Q - D).toNat) :
    16 ≤ (Q + c - (D + 0#64 * 16#64)).toNat := by
  bv_omega

set_option maxHeartbeats 400000 in
/-- `net-send` after the copy: it fills in descriptor 0 and offers it, writing
only the transmit queue's first descriptor, its available ring and the
card's notify register, before it waits. -/
theorem net_send_offer (k : Nat) (n : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) (D AV : Cell)
    (hq : TxQueue m D AV) :
    ∃ m' b, run Words.«net-send».code (k + 15) 26 ⟨s, n :: r, m, p, e⟩ =
        run Words.«net-send».code k 41 ⟨s, r, m', p, e⟩ ∧
      ∀ x : Cell, 16 ≤ (x - D).toNat → 20 ≤ (x - AV).toNat → 4 ≤ (x - (b + 80#64)).toNat →
        m' x = m x := by
  obtain ⟨hsz, hD, hAV, ⟨g1, g2⟩, hAD⟩ := hq
  generalize hQ : wordAddr "rx-vq" + 16#64 = Q at hsz hD hAV g1 g2
  have hsepD2 : 128 ≤ (Q - D).toNat := by bv_omega
  have hsep1 : 20 ≤ (Q + 24#64 - AV).toNat := by subst hAD; bv_omega
  have hsep2 : 8 ≤ (AV - (Q + 24#64)).toNat := by subst hAD; bv_omega
  obtain ⟨m1, h1, f1⟩ := desc_store_frame (wordAddr "tx-buf" + 8#64) (n + 12#64) 0#64 0#64
    Q 0#64 s r m p e D hD
  have e1 : rd m1 Q 8 = 8#64 := by
    rw [← hsz]; apply rd_congr; intro i hi; apply f1
    have := ofNat_small i 8 hi (by omega)
    exact record_apart0 Q D _ (by omega) g1 hsepD2
  have e2 : rd m1 (Q + 24#64) 8 = AV := by
    rw [← hAV]; apply rd_congr; intro i hi; apply f1
    rw [BitVec.add_assoc]
    exact record_apart0 Q D _ (avail_cell i hi) g1 hsepD2
  have hs1 : 2 * (8#64).toNat + 4 ≤ (Q + 24#64 - AV).toNat := by simpa using hsep1
  obtain ⟨m2, h2, f2⟩ := vq_submit_frame 0#64 Q (rd m1 (wordAddr "net-base" + 8#64) 8) 1#64 s r m1 p e
    8#64 AV e1 (by decide) (by decide) e2 hs1 hsep2
  refine ⟨m2, rd m1 (wordAddr "net-base" + 8#64) 8, ?_, ?_⟩
  · rw [show k + 15 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    simp only [Words.«net-send».code]
    generalize hd : Words.«desc!» = DS at h1 ⊢
    generalize hv : Words.«vq-submit» = VS at h2 ⊢
    simp [forth]
    rw [hQ, h1]
    dsimp only
    rw [h2]
  · intro x hx1 hx2 hx3
    have hx2' : 2 * (8#64).toNat + 4 ≤ (x - AV).toNat := by simpa using hx2
    rw [f2 x hx2' hx3, f1 x (by simpa using hx1)]

/-! ## The disk queue -/

/-- A disk's record and its 8-entry queue as `make-queues` and `new-vq` leave
them: the record (7 cells at dk) names the queue V; the queue's own record,
descriptor table and available ring follow V, all apart from the disk's
record. -/
structure BlkQueue (m : Mem) (dk V D AV : Cell) : Prop where
  vq : rd m (dk + 24#64) 8 = V
  size : rd m V 8 = 8#64
  desc : rd m (V + 16#64) 8 = D
  avail : rd m (V + 24#64) 8 = AV
  gap : 40 ≤ (D - V).toNat ∧ (D - V).toNat ≤ 55
  after : AV = D + 128#64
  apart : 204 ≤ (dk - V).toNat ∧ 56 ≤ (V - dk).toNat

/-- Eight bytes that a step left alone read the same. -/
theorem keep8 (m m' : Mem) (a : Cell) (P : Cell → Prop) (hf : ∀ x, P x → m' x = m x)
    (hp : ∀ c : Cell, c.toNat < 8 → P (a + c)) : rd m' a 8 = rd m a 8 := by
  apply rd_congr
  intro i hi
  exact hf _ (hp _ (by rw [ofNat_small i 8 hi (by omega)]; exact hi))

set_option maxHeartbeats 4000000 in
/-- The request header and status byte: 17 bytes from dk + 32. -/
theorem blk_header (buf type sector dk : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) :
    ∃ mh, (∀ k, run Words.«blk-request».code (k + 20) 0 ⟨dk :: sector :: type :: buf :: s, r, m, p, e⟩ =
        run Words.«blk-request».code k 20 ⟨type :: buf :: s, dk :: r, mh, p, e⟩) ∧
      ∀ x : Cell, 17 ≤ (x - (dk + 32#64)).toNat → mh x = m x := by
  refine ⟨wr (wr (wr (wr m (dk + 32#64 + 8#64) 8 sector) (dk + 32#64) 4 type) (dk + 32#64 + 4#64) 4 0#64)
    (dk + 48#64) 1 255#64, fun k => ?_, ?_⟩
  · rw [show k + 20 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    simp [forth]
  · intro x hx
    rw [wr_apply_other x 1 _ _ _ (fun j hj h => by have := ofNat_small j 1 hj (by omega); bv_omega),
      wr_apply_other x 4 _ _ _ (fun j hj h => by have := ofNat_small j 4 hj (by omega); bv_omega),
      wr_apply_other x 4 _ _ _ (fun j hj h => by have := ofNat_small j 4 hj (by omega); bv_omega),
      wr_apply_other x 8 _ _ _ (fun j hj h => by have := ofNat_small j 8 hj (by omega); bv_omega)]

set_option maxHeartbeats 4000000 in
/-- Descriptor 0: the request header. -/
theorem blk_desc0 (type buf dk : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) (V D : Cell)
    (hV : rd m (dk + 24#64) 8 = V) (hD : rd m (V + 16#64) 8 = D) :
    ∃ m1, (∀ k, run Words.«blk-request».code (k + 10) 20 ⟨type :: buf :: s, dk :: r, m, p, e⟩ =
        run Words.«blk-request».code k 30 ⟨type :: buf :: s, dk :: r, m1, p, e⟩) ∧
      ∀ x : Cell, 16 ≤ (x - (D + 0#64 * 16#64)).toNat → m1 x = m x := by
  obtain ⟨m1, h1, f1⟩ := desc_store_frame (dk + 32#64) 16#64 1#64 1#64 V 0#64 (type :: buf :: s) (dk :: r)
    m p e D hD
  refine ⟨m1, fun k => ?_, f1⟩
  rw [show k + 10 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  simp only [Words.«blk-request».code]
  generalize hd : Words.«desc!» = DS at h1 ⊢
  simp [forth, hV]
  rw [h1]

set_option maxHeartbeats 4000000 in
/-- The rest of the chain: for a flush, the status byte as descriptor 1; else
the caller's buffer as descriptor 1 and the status byte as descriptor 2. -/
theorem blk_chain (type buf dk : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) (V D : Cell)
    (hV : rd m (dk + 24#64) 8 = V) (hD : rd m (V + 16#64) 8 = D)
    (hV1 : ∀ m', (∀ x, 16 ≤ (x - (D + 1#64 * 16#64)).toNat → m' x = m x) →
      rd m' (dk + 24#64) 8 = V ∧ rd m' (V + 16#64) 8 = D) :
    ∃ j m2, (∀ k, run Words.«blk-request».code (k + j) 30 ⟨type :: buf :: s, dk :: r, m, p, e⟩ =
        run Words.«blk-request».code k 72 ⟨s, dk :: r, m2, p, e⟩) ∧
      ∀ x : Cell, 48 ≤ (x - (D + 16#64)).toNat → m2 x = m x := by
  by_cases hf : type = 4#64
  · subst hf
    obtain ⟨m1, h1, f1⟩ := desc_store_frame (dk + 48#64) 1#64 2#64 0#64 V 1#64 s (dk :: r) m p e D hD
    refine ⟨16, m1, fun k => ?_, fun x hx => f1 x (by bv_omega)⟩
    rw [show k + 16 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    simp only [Words.«blk-request».code]
    generalize hd : Words.«desc!» = DS at h1 ⊢
    simp [forth, hV]
    rw [h1]
  · have flags : ∃ fl : Cell, (type = 0#64 → fl = 3#64) ∧ (type ≠ 0#64 → fl = 1#64) :=
      if h : type = 0#64 then ⟨3#64, fun _ => rfl, fun h' => absurd h h'⟩
      else ⟨1#64, fun h' => absurd h' h, fun _ => rfl⟩
    obtain ⟨fl, hfl0, hfl1⟩ := flags
    obtain ⟨m1, h1, f1⟩ := desc_store_frame buf 1024#64 fl 2#64 V 1#64 s (dk :: r) m p e D hD
    obtain ⟨hV', hD'⟩ := hV1 m1 f1
    obtain ⟨m2, h2, f2⟩ := desc_store_frame (dk + 48#64) 1#64 2#64 0#64 V 2#64 s (dk :: r) m1 p e D hD'
    by_cases hi : type = 0#64
    · subst hi
      refine ⟨29, m2, fun k => ?_, fun x hx => ?_⟩
      · rw [show k + 29 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
        rw [hfl0 rfl] at h1
        simp only [Words.«blk-request».code]
        generalize hd : Words.«desc!» = DS at h1 h2 ⊢
        simp [forth, hV]
        rw [h1]
        dsimp only
        simp [forth, hV']
        rw [h2]
      · rw [f2 x (by bv_omega), f1 x (by bv_omega)]
    · refine ⟨28, m2, fun k => ?_, fun x hx => ?_⟩
      · rw [show k + 28 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
        rw [hfl1 hi] at h1
        simp only [Words.«blk-request».code]
        generalize hd : Words.«desc!» = DS at h1 h2 ⊢
        simp [forth, hV, hf, hi]
        rw [h1]
        dsimp only
        simp [forth, hV']
        rw [h2]
      · rw [f2 x (by bv_omega), f1 x (by bv_omega)]

set_option maxHeartbeats 4000000 in
/-- Offering the chain: the available ring and the disk's notify register. -/
theorem blk_offer (dk : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat) (V AV : Cell)
    (hV : rd m (dk + 24#64) 8 = V) (hsz : rd m V 8 = 8#64) (hAV : rd m (V + 24#64) 8 = AV)
    (hsep1 : 20 ≤ (V + 24#64 - AV).toNat) (hsep2 : 8 ≤ (AV - (V + 24#64)).toNat) :
    ∃ m', (∀ k, run Words.«blk-request».code (k + 9) 72 ⟨s, dk :: r, m, p, e⟩ =
        run Words.«blk-request».code k 81 ⟨s, dk :: r, m', p, e⟩) ∧
      ∀ x : Cell, 20 ≤ (x - AV).toNat → 4 ≤ (x - (rd m dk 8 + 80#64)).toNat → m' x = m x := by
  have hs1 : 2 * (8#64).toNat + 4 ≤ (V + 24#64 - AV).toNat := by simpa using hsep1
  obtain ⟨m', h, f⟩ := vq_submit_frame 0#64 V (rd m dk 8) 0#64 s (dk :: r) m p e 8#64 AV hsz
    (by decide) (by decide) hAV hs1 hsep2
  refine ⟨m', fun k => ?_, fun x hx hb => f x (by simpa using hx) hb⟩
  rw [show k + 9 = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  simp only [Words.«blk-request».code]
  generalize hv : Words.«vq-submit» = VS at h ⊢
  simp [forth, hV]
  rw [h]

/-! Where the steps' stores fall, against the cells read afterwards. -/

theorem hdr_dk (dk c : Cell) (hc : c.toNat < 8) : 17 ≤ (dk + 24#64 + c - (dk + 32#64)).toNat := by
  bv_omega

theorem hdr_V (dk V o c : Cell) (hc : c.toNat < 8) (ho : o.toNat ≤ 24) (a2 : 56 ≤ (V - dk).toNat) :
    17 ≤ (V + o + c - (dk + 32#64)).toNat := by
  bv_omega

theorem desc_dk (dk V D c i : Cell) (hc : c.toNat < 8) (hi : i.toNat < 8)
    (g1 : 40 ≤ (D - V).toNat) (g2 : (D - V).toNat ≤ 55)
    (a1 : 204 ≤ (dk - V).toNat) :
    16 ≤ (dk + 24#64 + c - (D + i * 16#64)).toNat := by
  bv_omega

theorem desc_V (V D o c i : Cell) (hc : c.toNat < 8) (ho : o.toNat ≤ 24) (hi : i.toNat < 8)
    (g1 : 40 ≤ (D - V).toNat) (g2 : (D - V).toNat ≤ 55) :
    16 ≤ (V + o + c - (D + i * 16#64)).toNat := by
  bv_omega

theorem chain_dk (dk V D c : Cell) (hc : c.toNat < 8)
    (g1 : 40 ≤ (D - V).toNat) (g2 : (D - V).toNat ≤ 55)
    (a1 : 204 ≤ (dk - V).toNat) :
    48 ≤ (dk + 24#64 + c - (D + 16#64)).toNat := by
  bv_omega

theorem chain_V (V D o c : Cell) (hc : c.toNat < 8) (ho : o.toNat ≤ 24)
    (g1 : 40 ≤ (D - V).toNat) (g2 : (D - V).toNat ≤ 55) :
    48 ≤ (V + o + c - (D + 16#64)).toNat := by
  bv_omega

theorem table_rest (x D : Cell) (h : 128 ≤ (x - D).toNat) : 48 ≤ (x - (D + 16#64)).toNat := by
  bv_omega

theorem table_first (x D : Cell) (h : 128 ≤ (x - D).toNat) : 16 ≤ (x - (D + 0#64 * 16#64)).toNat := by
  bv_omega

set_option maxHeartbeats 4000000 in
/-- `blk-request`, up to its wait: whatever the request, it writes only the
disk's request header and status byte (17 bytes at dk + 32), the disk
queue's descriptor table and available ring, and the disk's notify
register. -/
theorem blk_request_offer (buf type sector dk : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (V D AV : Cell) (hq : BlkQueue m dk V D AV) :
    ∃ j m' b, (∀ k, run Words.«blk-request».code (k + j) 0 ⟨dk :: sector :: type :: buf :: s, r, m, p, e⟩ =
        run Words.«blk-request».code k 81 ⟨s, dk :: r, m', p, e⟩) ∧
      ∀ x : Cell, 17 ≤ (x - (dk + 32#64)).toNat → 128 ≤ (x - D).toNat → 20 ≤ (x - AV).toNat →
        4 ≤ (x - (b + 80#64)).toNat → m' x = m x := by
  obtain ⟨hV, hsz, hD, hAV, ⟨g1, g2⟩, hAD, ⟨a1, a2⟩⟩ := hq
  have hsep1 : 20 ≤ (V + 24#64 - AV).toNat := by subst hAD; bv_omega
  have hsep2 : 8 ≤ (AV - (V + 24#64)).toNat := by subst hAD; bv_omega
  -- the header
  obtain ⟨mh, hA, fA⟩ := blk_header buf type sector dk s r m p e
  have kA : ∀ o : Cell, o.toNat ≤ 24 → rd mh (V + o) 8 = rd m (V + o) 8 := fun o ho =>
    keep8 m mh _ _ fA fun c hc => hdr_V dk V o c hc ho a2
  have hVh : rd mh (dk + 24#64) 8 = V := by
    rw [← hV]; exact keep8 m mh _ _ fA fun c hc => hdr_dk dk c hc
  have hszh : rd mh V 8 = 8#64 := by
    rw [← hsz, show V = V + 0#64 by simp]; exact kA _ (by decide)
  have hDh : rd mh (V + 16#64) 8 = D := by rw [← hD]; exact kA _ (by decide)
  have hAVh : rd mh (V + 24#64) 8 = AV := by rw [← hAV]; exact kA _ (by decide)
  -- descriptor 0
  obtain ⟨m1, hB, fB⟩ := blk_desc0 type buf dk s r mh p e V D hVh hDh
  have kB : ∀ o : Cell, o.toNat ≤ 24 → rd m1 (V + o) 8 = rd mh (V + o) 8 := fun o ho =>
    keep8 mh m1 _ _ fB fun c hc => desc_V V D o c 0#64 hc ho (by decide) g1 g2
  have hV1 : rd m1 (dk + 24#64) 8 = V := by
    rw [← hVh]; exact keep8 mh m1 _ _ fB fun c hc => desc_dk dk V D c 0#64 hc (by decide) g1 g2 a1
  have hD1 : rd m1 (V + 16#64) 8 = D := by rw [← hDh]; exact kB _ (by decide)
  -- the rest of the chain
  obtain ⟨j, m2, hC, fC⟩ := blk_chain type buf dk s r m1 p e V D hV1 hD1 fun m' f =>
    ⟨by rw [← hV1]; exact keep8 m1 m' _ _ f fun c hc => desc_dk dk V D c 1#64 hc (by decide) g1 g2 a1,
     by rw [← hD1]; exact keep8 m1 m' _ _ f fun c hc => desc_V V D 16#64 c 1#64 hc (by decide) (by decide) g1 g2⟩
  have kC : ∀ o : Cell, o.toNat ≤ 24 → rd m2 (V + o) 8 = rd m1 (V + o) 8 := fun o ho =>
    keep8 m1 m2 _ _ fC fun c hc => chain_V V D o c hc ho g1 g2
  have hV2 : rd m2 (dk + 24#64) 8 = V := by
    rw [← hV1]; exact keep8 m1 m2 _ _ fC fun c hc => chain_dk dk V D c hc g1 g2 a1
  have hsz2 : rd m2 V 8 = 8#64 := by
    rw [show V = V + 0#64 by simp, kC _ (by decide), kB _ (by decide), ← show V = V + 0#64 by simp]
    exact hszh
  have hAV2 : rd m2 (V + 24#64) 8 = AV := by
    rw [kC _ (by decide), kB _ (by decide)]; exact hAVh
  -- the offer
  obtain ⟨m3, hD', fD⟩ := blk_offer dk s r m2 p e V AV hV2 hsz2 hAV2 hsep1 hsep2
  refine ⟨j + 39, m3, rd m2 dk 8, fun k => ?_, fun x hx1 hx2 hx3 hx4 => ?_⟩
  · rw [show k + (j + 39) = k + 9 + j + 10 + 20 by omega, hA, hB, hC, hD']
  · rw [fD x hx3 hx4, fC x (table_rest x D hx2), fB x (table_first x D hx2), fA x hx1]

end OS4.Drivers

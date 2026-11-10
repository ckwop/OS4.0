import OS4.Words.NetArp
import OS4.Loops
import OS4.Memory
import OS4.FootPrims

/-!
# The ARP cache (V4)

ARP learns from every packet about us, so its stores take addresses from
the network and from memory: `arp-find` returns the address of an entry's
MAC, and `arp-learn` writes an entry chosen by `arp-next`, the next in
round robin. The generated footprints say "anywhere" for both. Here:
`arp-find` returns 0 or the MAC of one of the 8 entries, and changes
nothing (`arp_find_range`); and once `arp-learn` has decided to learn, it
writes only the cache (8 entries of 16 bytes) and `arp-next`, which it keeps
below 8, so long as it was below 8 (`arp_learn_store`).

DRAFT, not yet checked (branch v4-arp, 2026-11-10): `arp_entry_eq` checks;
`find_from` and `arp_find_range` failed their first checks (fixed since,
unchecked); a later theorem (`mac_in`, `mod_eq` or `mod8_lt`) ran past a
15-minute limit. Not in `make proofs` until it checks.
-/

namespace OS4.Arp
open OS4

abbrev arpCache : Cell := wordAddr "arp-cache" + 8#64
abbrev arpNext : Cell := wordAddr "arp-next" + 8#64

/-- The address of entry i's MAC (its second cell). -/
def IsMac (v : Cell) : Prop := ∃ i : Nat, i < 8 ∧ v = BitVec.ofNat 64 i * 16#64 + arpCache + 8#64

/-- `arp-entry` ( i -- addr ): entry i of the cache. -/
theorem arp_entry_eq (i : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    Words.«arp-entry» ⟨i :: s, r, m, u, e⟩ = .ok ⟨(i * 16#64 + arpCache) :: s, r, m, u, e⟩ := by
  -- by evaluation: `2 cells` is 16 (bv_decide here would have to prove two
  -- 64-bit multipliers equal, which it may not finish)
  rfl

/-- `arp-find`'s thread, with `arp-entry` left as AE. -/
noncomputable def findCode (AE : Sem) : List Ins := [.call Words.«#arp», .lit 0, .call Prim.pdo, .call Prim.dup,
  .call Prim.i, .call AE, .call Prim.fetch, .call Prim.equal, .zbranch 15, .call Prim.drop, .call Prim.i,
  .call AE, .call Words.«cell+», .call Prim.unloop, .exit, .loop 3, .call Prim.drop, .lit 0, .exit]

theorem findCode_eq : Words.«arp-find».code = findCode Words.«arp-entry» := rfl

/-- What `arp-entry` does, for any word standing in for it. -/
def EntryOK (AE : Sem) : Prop := ∀ (i : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat),
  AE ⟨i :: s, r, m, u, e⟩ = .ok ⟨(i * 16#64 + arpCache) :: s, r, m, u, e⟩

set_option maxHeartbeats 800000 in
/-- The loop from entry j on. -/
theorem find_from (AE : Sem) (hAE : EntryOK AE) (ip : Cell) (s r : List Cell) (m : Mem) (u : Cell)
    (e : Nat) : ∀ k j : Nat, j + k = 8 → 0 < k → ∃ n v,
      run (findCode AE) n 3 ⟨ip :: s, BitVec.ofNat 64 j :: 8#64 :: r, m, u, e⟩ =
        .ok ⟨v :: s, r, m, u, e⟩ ∧ (v = 0 ∨ IsMac v) := by
  unfold EntryOK at hAE
  intro k
  induction k with
  | zero => intro j _ hk; omega
  | succ k ih =>
    intro j hjk _
    by_cases hit : ip = rd m (BitVec.ofNat 64 j * 16#64 + arpCache) 8
    · refine ⟨12, BitVec.ofNat 64 j * 16#64 + arpCache + 8#64, ?_, Or.inr ⟨j, by omega, rfl⟩⟩
      simp [forth, findCode, hAE, ← hit]
    · by_cases hk : k = 0
      · subst hk
        have hj : j = 7 := by omega
        subst hj
        refine ⟨10, 0, ?_, Or.inl rfl⟩
        simp [forth, findCode, hAE, hit]
        all_goals (first | rfl | simp_all | bv_decide)
      · obtain ⟨n, v, hr, hv⟩ := ih (j + 1) (by omega) (by omega)
        refine ⟨n + 7, v, ?_, hv⟩
        have hne : ¬ BitVec.ofNat 64 j + 1#64 = 8#64 := by
          intro h
          have := congrArg BitVec.toNat h
          simp at this
          omega
        have hsucc : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp
          try omega
        rw [show n + 7 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
        simp [forth, findCode, hAE, hit, hne, hsucc]
        all_goals (first | exact hr | simpa [forth, findCode] using hr | simp_all)

/-- `arp-find` returns 0 or the address of an entry's MAC, and changes
nothing. -/
theorem arp_find_range (ip : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    ∃ v, Words.«arp-find» ⟨ip :: s, r, m, u, e⟩ = .ok ⟨v :: s, r, m, u, e⟩ ∧ (v = 0 ∨ IsMac v) := by
  have hAE : EntryOK Words.«arp-entry» := arp_entry_eq
  obtain ⟨n, v, hr, hv⟩ := find_from _ hAE ip s r m u e 8 0 rfl (by omega)
  refine ⟨v, ?_, hv⟩
  rw [show Words.«arp-find» = loopThread (findCode Words.«arp-entry») from rfl]
  generalize Words.«arp-entry» = AE at hAE hr ⊢
  apply loopThread_eq _ _ (n + 1 + 1 + 1) _ ?_ (by simp [outOfFuel])
  simpa [forth, findCode] using hr

/-- An entry's MAC lies in the cache: 6 bytes from it are among its 128. -/
theorem mac_in (v : Cell) (hv : IsMac v) (j : Nat) (hj : j < 6) :
    (v + BitVec.ofNat 64 j - arpCache).toNat < 128 := by
  obtain ⟨i, hi, rfl⟩ := hv
  have h1 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
  have h2 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
  bv_omega

/-- `arp-learn`'s thread, its calls left open. -/
noncomputable def learnCode (BS GM AF AE MD : Sem) : List Ins := [.call Prim.dup, .call Prim.zequal, .call Prim.over,
  .call BS, .call Prim.or, .lit 2, .call Prim.pick, .call GM, .call Prim.or, .zbranch 12,
  .call Words.«2drop», .exit, .call Prim.dup, .call AF, .call Words.«?dup», .zbranch 18,
  .call Words.«nip», .branch 30, .call Words.«arp-next», .call Prim.fetch, .call Prim.dup,
  .call Words.«1+», .call Words.«#arp», .call MD, .call Words.«arp-next», .call Prim.store,
  .call AE, .call Words.«tuck», .call Prim.store, .call Words.«cell+», .lit 6, .call Prim.cmove, .exit]

theorem learnCode_eq : Words.«arp-learn».code =
    learnCode Words.«bad-source?» Words.«group-mac?» Words.«arp-find» Words.«arp-entry» Words.«mod» :=
  rfl

/-- n mod 8, floored, as `mod` computes it. -/
def mod8 (n : Cell) : Cell :=
  if n - n.sdiv 8#64 * 8#64 ≠ 0 ∧ ((n - n.sdiv 8#64 * 8#64) ^^^ 8#64).msb
  then n - n.sdiv 8#64 * 8#64 + 8#64 else n - n.sdiv 8#64 * 8#64

theorem mod_eq (n : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    Words.«mod» ⟨8#64 :: n :: s, r, m, u, e⟩ = .ok ⟨mod8 n :: s, r, m, u, e⟩ := by
  unfold mod8
  by_cases h : n - n.sdiv 8#64 * 8#64 ≠ 0 ∧ ((n - n.sdiv 8#64 * 8#64) ^^^ 8#64).msb
  · simp only [Words.«mod», Words.«mod».code, thread, List.length_cons, List.length_nil, run,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Prim.slashmod, Prim.drop, if_pos h]
    simp
  · simp only [Words.«mod», Words.«mod».code, thread, List.length_cons, List.length_nil, run,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Prim.slashmod, Prim.drop, if_neg h]
    simp

/-- The round robin: after an index below 8, the next is below 8. -/
theorem mod8_lt (x : Cell) (hx : x.toNat < 8) : (mod8 (x + 1#64)).toNat < 8 := by
  have h8 : x = 0#64 ∨ x = 1#64 ∨ x = 2#64 ∨ x = 3#64 ∨ x = 4#64 ∨ x = 5#64 ∨ x = 6#64 ∨ x = 7#64 := by
    bv_omega
  rcases h8 with h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- Where `arp-learn` may store: the cache's 128 bytes, and `arp-next`. -/
def LearnWrites (a : Cell) : Prop := (a - arpCache).toNat < 128 ∨ (a - arpNext).toNat < 8

set_option maxHeartbeats 800000 in
/-- **`arp-learn`'s stores** (from where it has decided to learn: the MAC is
not a group address and the IP one a host may have): it updates the MAC of
an entry `arp-find` names, or takes the entry `arp-next` names, whose index
it advances. Either way it changes only the cache and `arp-next`, and leaves
`arp-next` below 8, given it was, and the cache apart from `arp-next`. -/
theorem arp_learn_store (BS GM AF : Sem) (ip mac : Cell) (s r : List Cell) (m : Mem) (u : Cell)
    (e : Nat) (v : Cell) (hF : AF ⟨ip :: ip :: mac :: s, r, m, u, e⟩ = .ok ⟨v :: ip :: mac :: s, r, m, u, e⟩)
    (hv : v = 0 ∨ IsMac v) (hn : (rd m arpNext 8).toNat < 8)
    (hapart : 128 ≤ (arpNext - arpCache).toNat ∧ 8 ≤ (arpCache - arpNext).toNat) :
    ∃ m', run (learnCode BS GM AF Words.«arp-entry» Words.«mod») 20 12 ⟨ip :: mac :: s, r, m, u, e⟩ =
        .ok ⟨s, r, m', u, e⟩ ∧
      (∀ a, ¬ LearnWrites a → m' a = m a) ∧ (rd m' arpNext 8).toNat < 8 := by
  have hAE : EntryOK Words.«arp-entry» := arp_entry_eq
  have hMD := mod_eq
  generalize Words.«arp-entry» = AE at hAE ⊢
  generalize Words.«mod» = MD at hMD ⊢
  unfold EntryOK at hAE
  by_cases hv0 : v = 0
  · -- a new entry, at arp-next
    subst hv0
    generalize hx : rd m arpNext 8 = x at hn
    generalize hE : x * 16#64 + arpCache = E
    refine ⟨Prim.cmoveM 6 (wr (wr m arpNext 8 (mod8 (x + 1#64))) E 8 ip) mac (E + 8#64), ?_, ?_, ?_⟩
    · subst hE
      simp [forth, learnCode, hF, hAE, hMD, hx]
      all_goals (first | rfl | simp_all)
    · intro a ha
      simp only [LearnWrites, not_or] at ha
      rw [cmoveM_other a 6 _ mac (E + 8#64) fun j hj haj => by
        apply ha.1
        have h1 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
        rw [haj]; bv_omega]
      rw [wr_apply_other a 8 _ E ip fun j hj haj => by
        apply ha.1
        have h1 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
        rw [haj]; bv_omega]
      rw [wr_apply_other a 8 m arpNext _ fun j hj haj => by
        apply ha.2
        have h1 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
        rw [haj]; bv_omega]
    · have hr : rd (Prim.cmoveM 6 (wr (wr m arpNext 8 (mod8 (x + 1#64))) E 8 ip) mac (E + 8#64))
          arpNext 8 = rd (wr m arpNext 8 (mod8 (x + 1#64))) arpNext 8 := by
        apply rd_congr
        intro i hi
        have h1 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
        rw [cmoveM_other _ 6 _ mac (E + 8#64) fun j hj haj => by
          have h2 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
          bv_omega]
        exact wr_apply_other _ 8 _ E ip fun j hj haj => by
          have h2 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
          bv_omega
      rw [hr, rd_wr_same]
      exact mod8_lt x hn
  · -- an entry it knows: the MAC is updated in place
    have hmac : IsMac v := hv.resolve_left hv0
    refine ⟨Prim.cmoveM 6 m mac v, ?_, ?_, ?_⟩
    · simp [forth, learnCode, hF, hv0]
    · intro a ha
      apply cmoveM_other a 6 m mac v
      intro j hj hav
      apply ha
      left
      rw [hav]
      exact mac_in v hmac j hj
    · rw [show rd (Prim.cmoveM 6 m mac v) arpNext 8 = rd m arpNext 8 from ?_]
      · exact hn
      · apply rd_congr
        intro i hi
        rw [cmoveM_other]
        intro j hj hij
        have := mac_in v hmac j hj
        have h1 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
        rw [← hij] at this
        bv_omega

/-- The same, for `arp-learn` as compiled, with `arp-find` as proven above. -/
theorem arp_learn_tail (ip mac : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hn : (rd m arpNext 8).toNat < 8)
    (hapart : 128 ≤ (arpNext - arpCache).toNat ∧ 8 ≤ (arpCache - arpNext).toNat) :
    ∃ m', run Words.«arp-learn».code 20 12 ⟨ip :: mac :: s, r, m, u, e⟩ = .ok ⟨s, r, m', u, e⟩ ∧
      (∀ a, ¬ LearnWrites a → m' a = m a) ∧ (rd m' arpNext 8).toNat < 8 := by
  obtain ⟨v, hF, hv⟩ := arp_find_range ip (ip :: mac :: s) r m u e
  rw [learnCode_eq]
  exact arp_learn_store _ _ _ ip mac s r m u e v hF hv hn hapart

end OS4.Arp

/-!
# Crash-safe records: the protocol

Part of milestone V3 (docs/verification.md). A record (records.fs) has two
copies, blocks n and n+1, each with a sequence number. `record@` takes the
copy with the higher number whose checksum holds; `record!` writes the next
number over the other copy, then syncs.

This file models the protocol, not yet the compiled words: one record's two
copies, each as what the disk holds for certain (`durable`), what has been
written since the last flush (`pending`, which a crash may keep, lose or
tear), and the block buffer (`cache`, `dirty`). Each write and the flush may
fail; a crash keeps any outcome a copy allows.

* `put_keeps`: whatever fails, `record!` keeps `Inv`, and when it returns
  its record is durable: a crash reads exactly it.
* `crash_reads`: under `Inv`, after a crash `record@` returns the last
  durable record or a newer one that was written, never anything else.
  With `put_keeps`, that is no garbage and durability.
* `evict0_keeps`, `evict1_keeps`, `drop_keeps`: another task's BLOCK, which
  may write one of these buffers back or reuse a clean one, keeps `Inv`.
* `old_loses`: without the sync at the start of `record!` (before
  DECISIONS.md #118), a failed write, a second `record!` and a crash lose the
  last durable record; `now_keeps`: the same failures now lose nothing.

Trusted, not proven:
* that the Forth words do what this model says (V3's next step links
  `record!` and the block words to it);
* that RECORD! is one step: records-lock keeps other records' writers out,
  and the only other task that touches these buffers is one evicting them,
  which writes back the copy SYNC was about to write anyway;
* that a torn copy fails its SipHash check (`Outcome` lets a pending copy
  become `none`, never another value). That holds with overwhelming
  probability, not certainty.
-/

namespace OS4.Records

/-- A copy's contents: its sequence number and data, or nothing valid. -/
abbrev Val := Option (Nat × Nat)

def seqOf : Val → Nat
  | some (s, _) => s
  | none => 0

structure Copy where
  durable : Val
  pending : Option Val
  cache : Option Val
  dirty : Bool

/-- What `copy-seq` sees: the buffer, else the disk. -/
def view (c : Copy) : Val := c.cache.getD (c.pending.getD c.durable)

/-- Write a dirty buffer back, if the write succeeds. -/
def wb (ok : Bool) (c : Copy) : Copy :=
  if c.dirty && ok then { c with pending := some (view c), dirty := false } else c

/-- A flush that finishes: what was written is durable. -/
def fl (c : Copy) : Copy := { c with durable := c.pending.getD c.durable, pending := none }

structure St where
  c0 : Copy          -- block n
  c1 : Copy          -- block n+1
  unsynced : Bool    -- a buffer changed, or a sync failed, since the last sync

/-- SYNC: each dirty buffer's write succeeds or fails (w0, w1), in either
order, and the flush happens only if every write did and it succeeds (f). -/
def sync (w0 w1 f : Bool) (st : St) : St × Bool :=
  let a := wb w0 st.c0
  let b := wb w1 st.c1
  if (!st.c0.dirty || w0) && (!st.c1.dirty || w1) && f then (⟨fl a, fl b, false⟩, true)
  else (⟨a, b, st.unsynced⟩, false)

/-- FILL-COPY: the new copy in a buffer, changed. -/
def fill (v : Val) (c : Copy) : Copy := { c with cache := some v, dirty := true }

/-- Which copy `record@` returns: the higher number, n+1 on a tie of zeros
being none anyway. -/
def read (o0 o1 : Val) : Val := if seqOf o0 < seqOf o1 then o1 else o0

/-- The write of the new copy, after the start: the next number, over the
older copy (as `(record!)` chooses), then SYNC. -/
def write (d : Nat) (g0 g1 g : Bool) (st : St) : St × Bool :=
  let s0 := seqOf (view st.c0)
  let s1 := seqOf (view st.c1)
  let v : Val := some (max s0 s1 + 1, d)
  if s0 < s1 then sync g0 g1 g { st with c0 := fill v st.c0, unsynced := true }
  else sync g0 g1 g { st with c1 := fill v st.c1, unsynced := true }

/-- RECORD! now: sync first if anything is unsynced (w0 w1 f say how that
goes), then write. The Bool is whether it returned. -/
def put (d : Nat) (w0 w1 f g0 g1 g : Bool) (st : St) : St × Bool :=
  if st.unsynced then
    match sync w0 w1 f st with
    | (st1, true) => write d g0 g1 g st1
    | (st1, false) => (st1, false)
  else write d g0 g1 g st

/-- RECORD! before #118: no sync first. -/
def putOld (d : Nat) (g0 g1 g : Bool) (st : St) : St × Bool := write d g0 g1 g st

/-- What a copy can hold after a crash. -/
def Outcome (c : Copy) (o : Val) : Prop :=
  o = c.durable ∨ (c.pending.isSome ∧ (o = none ∨ c.pending = some o))

/-! ## The invariant -/

/-- A copy that holds, for certain, a record numbered sL or more. -/
def Holds (sL : Nat) (c : Copy) : Prop :=
  sL ≤ seqOf c.durable ∧ c.pending = none ∧ c.dirty = false ∧ (c.cache = none ∨ c.cache = some c.durable)

/-- A clean buffer holds what the disk does; a dirty one holds something. -/
def Clean (c : Copy) : Prop :=
  (c.dirty = false → c.cache = none ∨ c.cache = some (c.pending.getD c.durable)) ∧
  (c.dirty = true → c.cache.isSome)

/-- The values written, and one more. -/
def Also (W : Val → Prop) (s d : Nat) (v : Val) : Prop := W v ∨ v = some (s, d)

/-- Every value in a copy was written. -/
def From (W : Val → Prop) (c : Copy) : Prop :=
  W c.durable ∧ (∀ v, c.pending = some v → W v) ∧ (∀ v, c.cache = some v → W v)

/-- The last durable record is numbered sL or more, and some copy holds it
for certain; with nothing unsynced, both copies are on the disk for certain. -/
def Inv (sL : Nat) (W : Val → Prop) (st : St) : Prop :=
  (Holds sL st.c0 ∨ Holds sL st.c1) ∧ Clean st.c0 ∧ Clean st.c1 ∧ From W st.c0 ∧ From W st.c1 ∧
  (st.unsynced = false → st.c0.pending = none ∧ st.c0.dirty = false ∧ st.c1.pending = none ∧ st.c1.dirty = false)

/-- A copy on the disk for certain, its buffer (if any) the same. -/
def Settled (c : Copy) : Prop :=
  c.pending = none ∧ c.dirty = false ∧ (c.cache = none ∨ c.cache = some c.durable)

/-! ## One copy -/

theorem view_settled {c : Copy} (h : Settled c) : view c = c.durable := by
  obtain ⟨hp, -, hc⟩ := h
  rcases hc with hc | hc <;> simp [view, hp, hc]

theorem settled_clean {c : Copy} (h : Settled c) : Clean c := by
  obtain ⟨hp, hd, hc⟩ := h
  refine ⟨fun _ => by simpa [hp] using hc, fun h' => by simp [hd] at h'⟩

theorem holds_settled {sL : Nat} {c : Copy} (h : Holds sL c) : Settled c := ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem wb_settled {c : Copy} (ok : Bool) (h : Settled c) : wb ok c = c := by
  simp [wb, h.2.1]

theorem fl_settled {c : Copy} (h : Settled c) : fl c = c := by
  obtain ⟨d, p, ca, di⟩ := c
  obtain ⟨hp, -, -⟩ := h
  simp_all [fl]

/-- A write that is not needed or succeeds, then the flush: the copy is
settled, holding what was in view. -/
theorem synced_copy {c : Copy} {w : Bool} (hc : Clean c) (hw : (!c.dirty || w) = true) :
    Settled (fl (wb w c)) ∧ (fl (wb w c)).durable = view c := by
  obtain ⟨d, p, ca, di⟩ := c
  obtain ⟨h1, h2⟩ := hc
  cases di <;> cases w <;> simp_all [wb, fl, view, Settled]
  · rcases h1 with h | h <;> simp [h]
  · rcases h1 with h | h <;> simp [h]
  · obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp h2
    simp

/-- A write that may fail, with no flush: the copy stays clean, and holds
only what it did. -/
theorem wb_clean {c : Copy} {w : Bool} (hc : Clean c) : Clean (wb w c) := by
  obtain ⟨d, p, ca, di⟩ := c
  obtain ⟨h1, h2⟩ := hc
  cases di <;> cases w <;> simp_all [wb, Clean, view]
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp h2
  simp

theorem wb_from {W : Val → Prop} {c : Copy} {w : Bool} (hc : Clean c) (h : From W c) : From W (wb w c) := by
  obtain ⟨d, p, ca, di⟩ := c
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨hd, hp, hca⟩ := h
  cases di <;> cases w <;> simp_all [wb, From, view]
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp h2
  simpa using hca

theorem fl_from {W : Val → Prop} {c : Copy} (h : From W c) : From W (fl c) := by
  obtain ⟨d, p, ca, di⟩ := c
  obtain ⟨hd, hp, hca⟩ := h
  refine ⟨?_, by simp [fl], hca⟩
  cases p <;> simp_all [fl]

theorem from_mono {W W' : Val → Prop} {c : Copy} (hW : ∀ v, W v → W' v) (h : From W c) : From W' c :=
  ⟨hW _ h.1, fun v hv => hW _ (h.2.1 v hv), fun v hv => hW _ (h.2.2 v hv)⟩

theorem outcome_from {W : Val → Prop} {c : Copy} {o : Val} (h : From W c) (ho : Outcome c o) :
    o = none ∨ W o := by
  rcases ho with rfl | ⟨-, rfl | hp⟩
  · exact .inr h.1
  · exact .inl rfl
  · exact .inr (h.2.1 _ hp)

theorem outcome_holds {sL : Nat} {c : Copy} {o : Val} (h : Holds sL c) (ho : Outcome c o) : o = c.durable := by
  rcases ho with rfl | ⟨hs, -⟩
  · rfl
  · simp [h.2.1] at hs

/-! ## After a crash -/

/-- Under the invariant, a crash leaves `record@` the last durable record or
a newer one, and only ever one that was written. -/
theorem crash_reads {sL : Nat} {W : Val → Prop} {st : St} {o0 o1 : Val} (h : Inv sL W st)
    (h0 : Outcome st.c0 o0) (h1 : Outcome st.c1 o1) :
    sL ≤ seqOf (read o0 o1) ∧ (read o0 o1 = none ∨ W (read o0 o1)) := by
  obtain ⟨hh, -, -, hw0, hw1, -⟩ := h
  constructor
  · rcases hh with hh | hh
    · have hs := hh.1
      rw [← outcome_holds hh h0] at hs
      unfold read; split <;> omega
    · have hs := hh.1
      rw [← outcome_holds hh h1] at hs
      unfold read; split <;> omega
  · unfold read; split
    · exact outcome_from hw1 h1
    · exact outcome_from hw0 h0

/-! ## RECORD! keeps the invariant -/

/-- The copy written over, once its write and the flush are done. -/
theorem target_synced (v : Val) (t : Copy) : fl (wb true (fill v t)) = ⟨v, none, some v, false⟩ := by
  simp [fl, wb, fill, view]

theorem target_clean (v : Val) (t : Copy) (gt : Bool) : Clean (wb gt (fill v t)) := by
  cases gt <;> simp [Clean, wb, fill, view]

theorem target_from {W : Val → Prop} {v : Val} {t : Copy} (gt : Bool) (hd : W t.durable)
    (hp : t.pending = none) (hv : W v) : From W (wb gt (fill v t)) := by
  cases gt <;> simp [From, wb, fill, view, hd, hp, hv]

theorem outcome_settled {c : Copy} {o : Val} (h : Settled c) (ho : Outcome c o) : o = c.durable := by
  rcases ho with rfl | ⟨hs, -⟩
  · rfl
  · simp [h.1] at hs

theorem sync_c0 {v : Val} {c0 c1 : Copy} {g0 g1 g : Bool} (hs1 : Settled c1) :
    sync g0 g1 g ⟨fill v c0, c1, true⟩ =
      if g0 && g then (⟨fl (wb true (fill v c0)), c1, false⟩, true) else (⟨wb g0 (fill v c0), c1, true⟩, false) := by
  have hn : c1.dirty = false := hs1.2.1
  cases g0 <;> cases g <;> simp [sync, fill, hn, wb_settled _ hs1, fl_settled hs1]

theorem sync_c1 {v : Val} {c0 c1 : Copy} {g0 g1 g : Bool} (hs0 : Settled c0) :
    sync g0 g1 g ⟨c0, fill v c1, true⟩ =
      if g1 && g then (⟨c0, fl (wb true (fill v c1)), false⟩, true) else (⟨c0, wb g1 (fill v c1), true⟩, false) := by
  have hn : c0.dirty = false := hs0.2.1
  cases g1 <;> cases g <;> simp [sync, fill, hn, wb_settled _ hs0, fl_settled hs0]

theorem holds_new (s d : Nat) : Holds s ⟨some (s, d), none, some (some (s, d)), false⟩ := by
  simp [Holds, seqOf]

theorem holds_of {sL : Nat} {c : Copy} (h : Settled c) (hs : sL ≤ seqOf c.durable) : Holds sL c :=
  ⟨hs, h.1, h.2.1, h.2.2⟩

/-- The write, from two copies on the disk for certain: if it returns, its
record is durable and is what a crash reads; if not, the copy holding the
last durable record was not touched. -/
theorem write_keeps {sL s : Nat} {W : Val → Prop} {d : Nat} {g0 g1 g : Bool} {st : St}
    (hs0 : Settled st.c0) (hs1 : Settled st.c1)
    (hL : sL ≤ seqOf st.c0.durable ∨ sL ≤ seqOf st.c1.durable) (hw0 : From W st.c0) (hw1 : From W st.c1)
    (hs : max (seqOf st.c0.durable) (seqOf st.c1.durable) + 1 = s) :
    ((write d g0 g1 g st).2 = true → Inv s (Also W s d) (write d g0 g1 g st).1 ∧
        ∀ o0 o1, Outcome (write d g0 g1 g st).1.c0 o0 → Outcome (write d g0 g1 g st).1.c1 o1 →
          read o0 o1 = some (s, d)) ∧
    ((write d g0 g1 g st).2 = false → Inv sL (Also W s d) (write d g0 g1 g st).1) := by
  generalize hr' : write d g0 g1 g st = r
  have hW : ∀ v, W v → Also W s d v := fun v h => .inl h
  have hv : Also W s d (some (s, d)) := .inr rfl
  have m0 : seqOf st.c0.durable < s := by omega
  have m1 : seqOf st.c1.durable < s := by omega
  have hr := hr'.symm
  simp only [write, view_settled hs0, view_settled hs1, hs] at hr
  have hnew : Settled ⟨some (s, d), none, some (some (s, d)), false⟩ := ⟨rfl, rfl, by simp⟩
  have hfrom : From (Also W s d) ⟨some (s, d), none, some (some (s, d)), false⟩ :=
    ⟨hv, fun v h => by simp at h, fun v h => by simp at h; subst h; exact hv⟩
  have e : seqOf (some (s, d)) = s := rfl
  by_cases hlt : seqOf st.c0.durable < seqOf st.c1.durable
  · -- over block n, the older
    rw [if_pos hlt, sync_c0 hs1] at hr
    have hL1 : sL ≤ seqOf st.c1.durable := by omega
    cases hg : (g0 && g)
    · rw [if_neg (by simp [hg])] at hr
      subst hr
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      exact ⟨.inr (holds_of hs1 hL1), target_clean _ _ _, settled_clean hs1,
        target_from _ (hW _ hw0.1) hs0.1 hv, from_mono hW hw1, fun h => by simp at h⟩
    · rw [if_pos (by simp [hg]), target_synced] at hr
      subst hr
      refine ⟨fun _ => ⟨⟨.inl (holds_new s d), settled_clean hnew, settled_clean hs1,
          hfrom, from_mono hW hw1, fun _ => ⟨rfl, rfl, hs1.1, hs1.2.1⟩⟩, ?_⟩, fun h => by simp at h⟩
      intro o0 o1 h0 h1
      rw [outcome_settled hnew h0, outcome_settled hs1 h1]
      unfold read
      rw [if_neg (by rw [e]; omega)]
  · -- over block n+1
    rw [if_neg hlt, sync_c1 hs0] at hr
    have hL0 : sL ≤ seqOf st.c0.durable := by omega
    cases hg : (g1 && g)
    · rw [if_neg (by simp [hg])] at hr
      subst hr
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      exact ⟨.inl (holds_of hs0 hL0), settled_clean hs0, target_clean _ _ _,
        from_mono hW hw0, target_from _ (hW _ hw1.1) hs1.1 hv, fun h => by simp at h⟩
    · rw [if_pos (by simp [hg]), target_synced] at hr
      subst hr
      refine ⟨fun _ => ⟨⟨.inr (holds_new s d), settled_clean hs0, settled_clean hnew,
          from_mono hW hw0, hfrom, fun _ => ⟨hs0.1, hs0.2.1, rfl, rfl⟩⟩, ?_⟩, fun h => by simp at h⟩
      intro o0 o1 h0 h1
      rw [outcome_settled hs0 h0, outcome_settled hnew h1]
      unfold read
      rw [if_pos (by rw [e]; omega)]

theorem inv_mono {sL : Nat} {W W' : Val → Prop} {st : St} (hW : ∀ v, W v → W' v) (h : Inv sL W st) :
    Inv sL W' st :=
  ⟨h.1, h.2.1, h.2.2.1, from_mono hW h.2.2.2.1, from_mono hW h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Under the invariant, with nothing unsynced, both copies are settled. -/
theorem settled_of_synced {sL : Nat} {W : Val → Prop} {st : St} (h : Inv sL W st) (hu : st.unsynced = false) :
    Settled st.c0 ∧ Settled st.c1 := by
  obtain ⟨-, ⟨c0a, -⟩, ⟨c1a, -⟩, -, -, hn⟩ := h
  obtain ⟨p0, d0, p1, d1⟩ := hn hu
  refine ⟨⟨p0, d0, ?_⟩, ⟨p1, d1, ?_⟩⟩
  · simpa [p0] using c0a d0
  · simpa [p1] using c1a d1

theorem holds_seq {sL : Nat} {W : Val → Prop} {st : St} (h : Inv sL W st) :
    sL ≤ seqOf (view st.c0) ∨ sL ≤ seqOf (view st.c1) := by
  rcases h.1 with h0 | h1
  · exact .inl (by rw [view_settled (holds_settled h0)]; exact h0.1)
  · exact .inr (by rw [view_settled (holds_settled h1)]; exact h1.1)

/-- RECORD!, whatever fails: it keeps the invariant, and if it returns, its
record is durable and is what a crash reads. -/
theorem put_keeps {sL : Nat} {W : Val → Prop} {st : St} (d : Nat) (w0 w1 f g0 g1 g : Bool)
    (h : Inv sL W st) :
    ∃ s, sL ≤ s ∧
      ((put d w0 w1 f g0 g1 g st).2 = true → Inv s (Also W s d) (put d w0 w1 f g0 g1 g st).1 ∧
        ∀ o0 o1, Outcome (put d w0 w1 f g0 g1 g st).1.c0 o0 → Outcome (put d w0 w1 f g0 g1 g st).1.c1 o1 →
          read o0 o1 = some (s, d)) ∧
      ((put d w0 w1 f g0 g1 g st).2 = false → Inv sL (Also W s d) (put d w0 w1 f g0 g1 g st).1) := by
  have hL := holds_seq h
  cases hu : st.unsynced
  · -- nothing unsynced: straight to the write
    obtain ⟨hs0, hs1⟩ := settled_of_synced h hu
    rw [view_settled hs0, view_settled hs1] at hL
    refine ⟨max (seqOf st.c0.durable) (seqOf st.c1.durable) + 1, by omega, ?_⟩
    simp only [put, hu]
    exact write_keeps hs0 hs1 hL h.2.2.2.1 h.2.2.2.2.1 rfl
  · -- the sync first
    obtain ⟨hh, hc0, hc1, hw0, hw1, -⟩ := h
    by_cases hok : ((!st.c0.dirty || w0) && (!st.c1.dirty || w1) && f) = true
    · have ⟨hs0, e0⟩ := synced_copy (w := w0) hc0 (by simp at hok; simp [hok.1.1])
      have ⟨hs1, e1⟩ := synced_copy (w := w1) hc1 (by simp at hok; simp [hok.1.2])
      have hsync : sync w0 w1 f st = (⟨fl (wb w0 st.c0), fl (wb w1 st.c1), false⟩, true) := by
        simp only [sync, if_pos hok]
      have hL' : sL ≤ seqOf (fl (wb w0 st.c0)).durable ∨ sL ≤ seqOf (fl (wb w1 st.c1)).durable := by
        rw [e0, e1]; exact hL
      refine ⟨max (seqOf (fl (wb w0 st.c0)).durable) (seqOf (fl (wb w1 st.c1)).durable) + 1, by omega, ?_⟩
      simp only [put, hu, hsync, if_true]
      exact write_keeps hs0 hs1 hL' (fl_from (wb_from hc0 hw0)) (fl_from (wb_from hc1 hw1)) rfl
    · have hsync : sync w0 w1 f st = (⟨wb w0 st.c0, wb w1 st.c1, true⟩, false) := by
        simp only [sync, if_neg hok, hu]
      refine ⟨sL, Nat.le_refl _, ?_⟩
      simp only [put, hu, hsync, if_true]
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      refine inv_mono (fun v hv => .inl hv) ⟨?_, wb_clean hc0, wb_clean hc1, wb_from hc0 hw0, wb_from hc1 hw1,
        fun h => by simp at h⟩
      rcases hh with h0 | h1
      · exact .inl (by rw [wb_settled _ (holds_settled h0)]; exact h0)
      · exact .inr (by rw [wb_settled _ (holds_settled h1)]; exact h1)

/-! ## Other tasks

While RECORD! is not running (and in the model, between its steps), another
task's BLOCK may evict one of these buffers, writing it back if dirty, or
reuse a clean one. Neither breaks the invariant. -/

theorem evict0_keeps {sL : Nat} {W : Val → Prop} {st : St} (h : Inv sL W st) :
    Inv sL W { st with c0 := wb true st.c0 } := by
  obtain ⟨hh, hc0, hc1, hw0, hw1, hn⟩ := h
  refine ⟨?_, wb_clean hc0, hc1, wb_from hc0 hw0, hw1, fun hu => ?_⟩
  · rcases hh with h0 | h1
    · exact .inl (by simp only; rw [wb_settled _ (holds_settled h0)]; exact h0)
    · exact .inr h1
  · obtain ⟨p0, d0, p1, d1⟩ := hn hu
    simp only
    rw [wb_settled true ⟨p0, d0, by simpa [p0] using hc0.1 d0⟩]
    exact ⟨p0, d0, p1, d1⟩

theorem evict1_keeps {sL : Nat} {W : Val → Prop} {st : St} (h : Inv sL W st) :
    Inv sL W { st with c1 := wb true st.c1 } := by
  obtain ⟨hh, hc0, hc1, hw0, hw1, hn⟩ := h
  refine ⟨?_, hc0, wb_clean hc1, hw0, wb_from hc1 hw1, fun hu => ?_⟩
  · rcases hh with h0 | h1
    · exact .inl h0
    · exact .inr (by simp only; rw [wb_settled _ (holds_settled h1)]; exact h1)
  · obtain ⟨p0, d0, p1, d1⟩ := hn hu
    simp only
    rw [wb_settled true ⟨p1, d1, by simpa [p1] using hc1.1 d1⟩]
    exact ⟨p0, d0, p1, d1⟩

/-- Reusing a clean buffer: the copy is read from the disk next time. -/
def drop (c : Copy) : Copy := if c.dirty then c else { c with cache := none }

theorem drop_clean {c : Copy} (h : Clean c) : Clean (drop c) := by
  obtain ⟨du, p, ca, di⟩ := c
  cases di <;> simp_all [drop, Clean]

theorem drop_from {W : Val → Prop} {c : Copy} (h : From W c) : From W (drop c) := by
  obtain ⟨du, p, ca, di⟩ := c
  cases di <;> simp_all [drop, From]

theorem drop_holds {sL : Nat} {c : Copy} (h : Holds sL c) : Holds sL (drop c) := by
  obtain ⟨du, p, ca, di⟩ := c
  obtain ⟨h1, h2, h3, -⟩ := h
  simp_all [drop, Holds]

theorem drop_keeps {sL : Nat} {W : Val → Prop} {st : St} (h : Inv sL W st) :
    Inv sL W { st with c0 := drop st.c0, c1 := drop st.c1 } := by
  obtain ⟨hh, hc0, hc1, hw0, hw1, hn⟩ := h
  refine ⟨hh.imp drop_holds drop_holds, drop_clean hc0, drop_clean hc1, drop_from hw0, drop_from hw1,
    fun hu => ?_⟩
  obtain ⟨p0, d0, p1, d1⟩ := hn hu
  simp [drop, p0, d0, p1, d1]

/-! ## The old RECORD! loses a record -/

def empty : Copy := ⟨none, none, none, false⟩
def start : St := ⟨empty, empty, false⟩

/-- Record 1 written and synced; record 2's write fails; record 3's write of
its own copy reaches the disk but the other write fails; then a crash tears
the copy record 3 was written over. Record 1 was durable, and is lost. -/
theorem old_loses :
    let a := putOld 1 true true true start
    let b := putOld 2 false true true a.1
    let c := putOld 3 false true true b.1
    a.2 = true ∧ Inv 1 (fun _ => True) a.1 ∧ b.2 = false ∧ c.2 = false ∧
    Outcome c.1.c0 none ∧ Outcome c.1.c1 none ∧ seqOf (read none none) < 1 := by
  simp [putOld, write, sync, wb, fl, fill, view, seqOf, start, empty, Outcome, read, Inv, Holds, Clean, From]

/-- The same failures with RECORD! as it is now: record 3 stops at its
first sync, and a crash still reads record 1. -/
theorem now_keeps :
    let a := put 1 true true true true true true start
    let b := put 2 true true true false true true a.1
    let c := put 3 false true true false true true b.1
    ∀ o0 o1, Outcome c.1.c0 o0 → Outcome c.1.c1 o1 → read o0 o1 = some (1, 1) := by
  simp [put, write, sync, wb, fl, fill, view, seqOf, start, empty, Outcome, read]

end OS4.Records

import OS4.Words.Records

/-!
# A record's sequence numbers: reading and writing agree

A record (records.fs) has two copies, each with a sequence number. `record@`
reads the copy `newer?` calls the newer; `record!` writes `next-seq` of that
one's number over the other copy. Before DECISIONS.md #146 the write chose its
number with a signed `max` and the read compared with an unsigned `u<`, so a
copy numbered 2^63 or more made every later write read back as older than it
(docs/defects.md, 40); nothing handled the count wrapping to 0 (never written).

Here, on the compiled words:
* `next_seq_eq`, `newer_eq`: what `next-seq` and `newer?` compute;
* `nextSeq_ne`: the next number is never 0, which means never written;
* `newer_next`, `next_not_older`: whatever the newer copy's number s, the copy
  written next (`nextSeq s`) is the newer of the two, whichever block it is in.
  So the record just written is the one `record@` reads, even across the wrap.
-/

namespace OS4.RecordSeq
open OS4

/-- `newer? ( s0 s1 -- flag )`: copy 1 is the newer. 0 is never written, older
than anything; otherwise s1 - s0, taken as signed, is positive. -/
def newer (s0 s1 : Cell) : Bool :=
  if s0 = 0 then s1 != 0 else if s1 = 0 then false else (0 : Cell).slt (s1 - s0)

/-- `next-seq ( s -- s' )`: one more, skipping 0. -/
def nextSeq (s : Cell) : Cell := if s + 1 = 0 then 1 else s + 1

theorem next_seq_eq (x : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    Words.«next-seq» ⟨x :: s, r, m, u, e⟩ = .ok ⟨nextSeq x :: s, r, m, u, e⟩ := by
  by_cases h : x + 1#64 = 0#64
  · simp [forth, nextSeq, h]
  · simp [forth, nextSeq, h]

theorem newer_eq (s0 s1 : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    Words.«newer?» ⟨s1 :: s0 :: s, r, m, u, e⟩ = .ok ⟨flag (newer s0 s1) :: s, r, m, u, e⟩ := by
  by_cases h0 : s0 = 0#64 <;> by_cases h1 : s1 = 0#64 <;> simp [forth, newer, h0, h1]

theorem nextSeq_ne (x : Cell) : nextSeq x ≠ 0 := by
  unfold nextSeq; split
  · decide
  · assumption

/-- Written over copy 1, the new copy is the newer. -/
theorem newer_next (x : Cell) : newer x (nextSeq x) = true := by
  have hn := nextSeq_ne x
  unfold newer
  by_cases h0 : x = 0
  · subst h0
    decide
  · simp only [h0, hn, if_false]
    unfold nextSeq
    split
    · have : x = -1 := by bv_omega
      subst this; decide
    · have : x + 1 - x = 1 := by bv_omega
      rw [this]; decide

/-- Written over copy 0, the other copy is not the newer. -/
theorem next_not_older (x : Cell) : newer (nextSeq x) x = false := by
  have hn := nextSeq_ne x
  unfold newer
  by_cases h0 : x = 0
  · subst h0
    decide
  · simp only [h0, hn, if_false]
    unfold nextSeq
    split
    · have : x = -1 := by bv_omega
      subst this; decide
    · have : x - (x + 1) = -1 := by bv_omega
      rw [this]; decide

end OS4.RecordSeq

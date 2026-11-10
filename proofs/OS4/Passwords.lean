import OS4.Words.Crypto

/-!
# A password check ends, whatever the stored hash holds

`password?` takes the iteration count from the stored hash (its first cell),
which comes from the data disk. A count of 0 or less once ran PBKDF2 for 2^64
iterations while holding `hash-lock`, so every later login or hash in the
system waited for good (docs/defects.md, 34; DECISIONS.md #143). Now a count
outside 1 to `max-iterations` (2^21) is refused before any hashing:
`(password?)` answers false, with the stack and memory otherwise as they were
(`password_bad_count`). With a count in range it runs at most 2^21
iterations, each of which pauses.
-/

namespace OS4.Passwords
open OS4

/-- A stored count c with c - 1 not below 2^21 (unsigned), that is c = 0,
c above 2^21, or any negative c: `(password?)` answers false at once, with
no store and no call to PBKDF2. -/
theorem password_bad_count (pw l a : Cell) (s r : List Cell) (m : Mem) (p : Cell) (e : Nat)
    (h : BitVec.ult (rd m pw 8 - 1#64) 2097152#64 = false) :
    Words.«(password?)» ⟨pw :: l :: a :: s, r, m, p, e⟩ = .ok ⟨0 :: s, r, m, p, e⟩ := by
  simp only [Words.«(password?)», Words.«(password?)».code]
  generalize Words.«(pbkdf2)» = PB
  generalize Words.«bytes-differ» = BD
  generalize Words.«pw-check» = PC
  simp [forth, h]

end OS4.Passwords

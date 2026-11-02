import OS4.Specs.Core
import OS4.Foots.Core

/-!
# Words run under LOCKED

`['] word sem locked` runs word holding a semaphore (core.fs; DECISIONS.md
#76). EXECUTE and CATCH run whatever an xt's `dispatch` is, which the model
leaves unknown, so a certificate takes the literal xt, the semaphore and
LOCKED as one step (`seg3`), and needs to know what that xt runs: `Runs`,
the one fact here that is trusted, not proven. The generator states it for
each such xt, and every theorem that rests on it takes it as an instance
argument, so it shows in the theorem's statement.

LOCKED catches whatever the word throws, releases the semaphore and throws
it again, so if it returns, the word returned: its stack effect is the
word's (`locked_seg_spec`), and it writes what the word writes and the
semaphore's two cells (`locked_seg_foot`).
-/

namespace OS4

/-- The xt of the word named n (`wordAddr n`) runs f: what the dumper and
the generator say of each word the boot files hand to LOCKED. Trusted. -/
class Runs (n : String) (f : Sem) : Prop where
  runs : dispatch (wordAddr n) = f

/-- `['] word sem locked`, as one step, has word's stack effect. -/
theorem locked_seg_spec {v : Cell} {g P : Sem} {k j : Nat}
    (hv : dispatch v = g) (hg : Spec g k j 0 0) (hP : Spec P 0 1 0 0) :
    Spec (seg3 v P Words.«locked») k j 0 0 := by
  intro xs zs s r m u e hx hz
  obtain rfl : zs = [] := List.eq_nil_of_length_eq_zero hz
  have hP' := hP [] [] (v :: (xs ++ s)) r m u e rfl rfl
  simp only [List.nil_append] at hP' ⊢
  simp only [seg3]
  split
  · rename_i s1 h1
    rw [h1] at hP'
    obtain ⟨⟨ys1, hl1, hd1⟩, ⟨ws1, hw1, hr1⟩, hu1⟩ := hP'
    obtain ⟨a, rfl⟩ : ∃ a, ys1 = [a] := by
      match ys1, hl1 with
      | [a], _ => exact ⟨a, rfl⟩
    obtain rfl : ws1 = [] := List.eq_nil_of_length_eq_zero hw1
    obtain ⟨ds1, rs1, m1, u1, e1⟩ := s1
    simp only [List.singleton_append, List.nil_append] at hd1 hr1 hu1
    subst ds1 rs1 u1
    -- LOCKED: dup >r get catch r> release throw
    simp only [Words.«locked», Words.«locked».code, thread, run, List.length_cons, List.length_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Prim.dup, Prim.tor]
    split
    · rename_i s2 h2
      have hG := Words.«get».spec [a] [] (v :: (xs ++ s)) (a :: r) m1 u e1 rfl rfl
      simp only [List.singleton_append, List.nil_append, h2, Out] at hG
      obtain ⟨⟨ys2, hl2, hd2⟩, ⟨ws2, hw2, hr2⟩, hu2⟩ := hG
      obtain rfl : ys2 = [] := List.eq_nil_of_length_eq_zero hl2
      obtain rfl : ws2 = [] := List.eq_nil_of_length_eq_zero hw2
      obtain ⟨ds2, rs2, m2, u2, e2⟩ := s2
      simp only [List.nil_append] at hd2 hr2 hu2
      subst ds2 rs2 u2
      have hG2 := hg xs [] s (a :: r) m2 u e2 hx rfl
      simp only [List.nil_append] at hG2
      simp only [catchM, hv]
      cases h3 : g ⟨xs ++ s, a :: r, m2, u, e2⟩ with
      | ok s3 =>
        rw [h3] at hG2
        obtain ⟨⟨ys3, hl3, hd3⟩, ⟨ws3, hw3, hr3⟩, hu3⟩ := hG2
        obtain rfl : ws3 = [] := List.eq_nil_of_length_eq_zero hw3
        obtain ⟨ds3, rs3, m3, u3, e3⟩ := s3
        simp only [List.nil_append] at hd3 hr3 hu3
        subst ds3 rs3 u3
        simp only [Prim.rfrom]
        split
        · rename_i s4 h4
          have hR := Words.«release».spec [a] [] (0 :: (ys3 ++ s)) r m3 u e3 rfl rfl
          simp only [List.singleton_append, List.nil_append, h4, Out] at hR
          obtain ⟨⟨ys4, hl4, hd4⟩, ⟨ws4, hw4, hr4⟩, hu4⟩ := hR
          obtain rfl : ys4 = [] := List.eq_nil_of_length_eq_zero hl4
          obtain rfl : ws4 = [] := List.eq_nil_of_length_eq_zero hw4
          obtain ⟨ds4, rs4, m4, u4, e4⟩ := s4
          simp only [List.nil_append] at hd4 hr4 hu4
          subst ds4 rs4 u4
          simp only [throwM, if_true, Out]
          refine ⟨⟨ys3, hl3, rfl⟩, ?_, ?_⟩ <;> simp
        · simp [Out]
      | error fl =>
        simp only
        cases hn : fl.err.code with
        | none => simp [Out]
        | some n =>
          have hn0 : ¬ (n = 0#64) := Err.code_ne_zero hn
          simp only [Prim.rfrom]
          split
          · rename_i s4 h4
            have hR := Words.«release».spec [a] [] (n :: (List.map (junk fl.ext) (List.range (xs ++ s).length)))
              r fl.mem u fl.ext rfl rfl
            simp only [List.singleton_append, List.nil_append, h4, Out] at hR
            obtain ⟨⟨ys4, hl4, hd4⟩, -, -⟩ := hR
            obtain rfl : ys4 = [] := List.eq_nil_of_length_eq_zero hl4
            obtain ⟨ds4, rs4, m4, u4, e4⟩ := s4
            simp only [List.nil_append] at hd4
            subst hd4
            simp [throwM, hn0, Out]
          · simp [Out]
    · simp [Out]
  · simp [Out]

/-- GET and RELEASE write only the semaphore's two cells, and take it off
the stack. -/
theorem sem_word {f : Sem} (hf : Foot f 1 0 0 0 [⟨.arg 0 8, .num 8⟩, ⟨.arg 0 0, .num 8⟩] [] [])
    (a : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) :
    (∀ x, Quiet x → 16 ≤ (x - a).toNat → resMem (f ⟨a :: s, r, m, u, e⟩) x = m x) ∧
    (∀ st, f ⟨a :: s, r, m, u, e⟩ = .ok st → st.ds = s ∧ st.rs = r ∧ st.up = u) := by
  have h := hf [a] [] s r m u e rfl rfl
  simp only [List.singleton_append, List.nil_append] at h
  refine ⟨fun x hq h16 => h.1 x hq ?_, fun st hst => ?_⟩
  · rintro ⟨reg, hreg, hh⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hreg
    rcases hreg with rfl | rfl
    · have := hh (a + 8) 8 (by simp [Val.eval]) (by simp [Val.eval])
      bv_omega
    · have := hh a 8 (by simp [Val.eval]) (by simp [Val.eval])
      bv_omega
  · have h2 := h.2
    rw [hst] at h2
    obtain ⟨hl, hd, -, hrl, hrd, -, hup⟩ := h2
    refine ⟨?_, ?_, hup⟩
    · simpa using hd
    · simpa using hrd

/-- `['] word sem locked`, as one step, writes what word writes and the
semaphore's two cells, and leaves what word leaves. The semaphore word P
writes nothing and pushes the semaphore, `wordAddr n + o`. -/
theorem locked_seg_foot {v : Cell} {g P : Sem} {k j : Nat} {regs : List Reg} {dout : List Val}
    {n : String} {o : Cell}
    (hv : dispatch v = g) (hg : Foot g k j 0 0 regs dout []) (hP : Foot P 0 1 0 0 [] [.word n o] [])
    (hPn : NoWrite P) :
    NoWrite P ∧ Foot (seg3 v P Words.«locked») k j 0 0 (regs ++ [⟨.word n o, .num 16⟩]) dout [] := by
  refine ⟨hPn, ?_⟩
  intro xs zs s r m u e hx hz
  obtain rfl : zs = [] := List.eq_nil_of_length_eq_zero hz
  simp only [List.nil_append]
  -- outside the word's regions and the semaphore's 16 bytes, where the world is quiet
  have outside : ∀ a, Quiet a → ¬ Writes (regs ++ [⟨.word n o, .num 16⟩]) ⟨xs, [], u⟩ a →
      ¬ Writes regs ⟨xs, [], u⟩ a ∧ 16 ≤ (a - (wordAddr n + o)).toNat := by
    intro a _ hw
    refine ⟨fun h => hw ?_, ?_⟩
    · obtain ⟨reg, hreg, hh⟩ := h
      exact ⟨reg, List.mem_append_left _ hreg, hh⟩
    · apply Classical.byContradiction
      intro hlt
      apply hw
      refine ⟨⟨.word n o, .num 16⟩, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      intro b l hb hl
      simp only [Val.eval, Option.some.injEq] at hb hl
      subst hb hl
      have h16 : (16 : Cell).toNat = 16 := rfl
      omega
  have hPv := hP [] [] (v :: (xs ++ s)) r m u e rfl rfl
  have hPm := hPn ⟨v :: (xs ++ s), r, m, u, e⟩
  simp only [List.nil_append] at hPv
  simp only [seg3]
  split
  · rename_i s1 h1
    rw [h1] at hPv hPm
    simp only [resMem] at hPm
    obtain ⟨-, hl1, hd1, ha1, hrl1, hrd1, -, hu1⟩ := hPv
    obtain ⟨ds1, rs1, m1, u1, e1⟩ := s1
    simp only at hl1 hd1 ha1 hrl1 hrd1 hu1 hPm
    subst u1 m1
    obtain ⟨a, rfl⟩ : ∃ a, ds1 = a :: (v :: (xs ++ s)) := by
      match ds1, hl1, hd1 with
      | a :: t, _, hd => exact ⟨a, by simpa using hd⟩
    have ha : a = wordAddr n + o := (agree_cons.mp ha1).1 _ (by simp [Val.eval])
    subst ha
    have hrs1 : rs1 = r := by simpa using hrd1
    subst rs1
    -- LOCKED: dup >r get catch r> release throw
    simp only [Words.«locked», Words.«locked».code, thread, run, List.length_cons, List.length_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Prim.dup, Prim.tor]
    have ⟨gk, gs⟩ := sem_word Words.«get».foot (wordAddr n + o) (v :: (xs ++ s)) ((wordAddr n + o) :: r) m u e1
    split
    · rename_i s2 h2
      rw [h2] at gk
      obtain ⟨hd2, hr2, hu2⟩ := gs _ h2
      obtain ⟨ds2, rs2, m2, u2, e2⟩ := s2
      simp only [resMem] at gk hd2 hr2 hu2
      subst ds2 rs2 u2
      have hgf := hg xs [] s ((wordAddr n + o) :: r) m2 u e2 hx rfl
      simp only [List.nil_append] at hgf
      simp only [catchM, hv]
      cases h3 : g ⟨xs ++ s, (wordAddr n + o) :: r, m2, u, e2⟩ with
      | ok s3 =>
        rw [h3] at hgf
        obtain ⟨gkept, hl3, hd3, ha3, hrl3, hrd3, -, hu3⟩ := hgf
        obtain ⟨ds3, rs3, m3, u3, e3⟩ := s3
        simp only [resMem] at gkept hl3 hd3 ha3 hrl3 hrd3 hu3
        subst u3
        have hrs3 : rs3 = (wordAddr n + o) :: r := by simpa using hrd3
        subst rs3
        simp only
        simp only [Prim.rfrom]
        have ⟨rk, rs⟩ := sem_word Words.«release».foot (wordAddr n + o) (0 :: ds3) r m3 u e3
        split
        · rename_i s4 h4
          rw [h4] at rk
          obtain ⟨hd4, hr4, hu4⟩ := rs _ h4
          obtain ⟨ds4, rs4, m4, u4, e4⟩ := s4
          simp only [resMem] at rk hd4 hr4 hu4
          subst ds4 rs4 u4
          simp only [throwM, if_true, run]
          refine ⟨fun a hq hw => ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
          · obtain ⟨hreg, h16⟩ := outside a hq hw
            simp only [resMem]
            rw [rk a hq h16, gkept a hq hreg, gk a hq h16]
          · exact hl3
          · exact hd3
          · exact ha3
          · simp
          · simp
          · exact agree_nil _ _
        · rename_i fl h4
          rw [h4] at rk
          refine ⟨fun a hq hw => ?_, trivial⟩
          obtain ⟨hreg, h16⟩ := outside a hq hw
          rw [rk a hq h16, gkept a hq hreg, gk a hq h16]
      | error fl =>
        rw [h3] at hgf
        obtain ⟨gkept, -⟩ := hgf
        simp only [resMem] at gkept
        simp only
        cases hc : fl.err.code with
        | some c =>
          have hc0 : ¬ (c = 0#64) := Err.code_ne_zero hc
          simp only [Prim.rfrom]
          have ⟨rk, rs⟩ := sem_word Words.«release».foot (wordAddr n + o)
            (c :: List.map (junk fl.ext) (List.range (xs ++ s).length)) r fl.mem u fl.ext
          split
          · rename_i s4 h4
            rw [h4] at rk
            obtain ⟨hd4, hr4, hu4⟩ := rs _ h4
            obtain ⟨ds4, rs4, m4, u4, e4⟩ := s4
            simp only [resMem] at rk hd4 hr4 hu4
            subst ds4 rs4 u4
            simp only [throwM]
            rw [if_neg (show ¬ (c = 0) from hc0)]
            refine ⟨fun a hq hw => ?_, trivial⟩
            obtain ⟨hreg, h16⟩ := outside a hq hw
            simp only [resMem]
            rw [rk a hq h16, gkept a hq hreg, gk a hq h16]
          · rename_i fl2 h4
            rw [h4] at rk
            refine ⟨fun a hq hw => ?_, trivial⟩
            obtain ⟨hreg, h16⟩ := outside a hq hw
            rw [rk a hq h16, gkept a hq hreg, gk a hq h16]
        | none =>
          refine ⟨fun a hq hw => ?_, trivial⟩
          obtain ⟨hreg, h16⟩ := outside a hq hw
          simp only [resMem]
          rw [gkept a hq hreg, gk a hq h16]
    · rename_i fl h2
      rw [h2] at gk
      refine ⟨fun a hq hw => ?_, trivial⟩
      obtain ⟨-, h16⟩ := outside a hq hw
      exact gk a hq h16
  · rename_i fl h1
    rw [h1] at hPm
    refine ⟨fun a _ _ => ?_, trivial⟩
    simpa [resMem] using congrFun hPm a

end OS4

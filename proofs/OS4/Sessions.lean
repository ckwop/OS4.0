import OS4.Words.NetRepl
import OS4.Loops
import OS4.Memory

/-!
# A session gives its connection and its door's place back

Part of milestone V6 (docs/verification.md). `session` ( conn door -- ), in
net/repl.fs, runs a door's word with the connection as the task's terminal:
`(session)` sets the terminal up and runs it, under CATCH. Whatever that
does, returning or throwing (even before the terminal is set up, if the
client has gone, DECISIONS.md #117), `session_closes` proves that SESSION
gives the door's place back (its count is one less than when the session
began) and goes on to `close-connection` with the connection, with the
return stack as the caller left it; then `tidy-session` puts the task back.

The work and `farewell`, which says why a session ended, are any words at
all (`dispatch` is opaque), so long as they leave the door's count alone.
The exception is a failure CATCH does not catch: not finishing, or BYE.

Trusted, not proven here: that `close-connection` itself finishes, and that
the cleanup runs before the watchdog could stop it (THROW gives the catcher
a fresh allowance, core.fs).
-/

namespace OS4.Sessions
open OS4

/-- xt leaves the cell at c alone and, when it returns, the return stack and
the user area too. -/
def Keeps (xt c : Cell) : Prop :=
  ∀ st : S,
    match dispatch xt st with
    | .ok st' => rd st'.mem c 8 = rd st.mem c 8 ∧ st'.rs = st.rs ∧ st'.up = st.up
    | .error f => rd f.mem c 8 = rd st.mem c 8

/-- The cell at c is outside the user area at u (512 bytes). -/
def Outside (u c : Cell) : Prop := 512 ≤ c - u ∧ 8 ≤ u - c

theorem rd_wr_user {u c : Cell} (h : Outside u c) (m : Mem) (k v : Cell) (hk : k ≤ 504) :
    rd (wr m (k + u) 8 v) c 8 = rd m c 8 := by
  obtain ⟨h1, h2⟩ := h
  apply rd_wr_other <;> bv_decide

theorem rd_wr_user' {u c : Cell} (h : Outside u c) (m : Mem) (k v : Cell) (hk : k ≤ 504) :
    rd (wr m (u + k) 8 v) c 8 = rd m c 8 := by
  rw [BitVec.add_comm]; exact rd_wr_user h m k v hk

theorem rd_wr_user0 {u c : Cell} (h : Outside u c) (m : Mem) (v : Cell) :
    rd (wr m u 8 v) c 8 = rd m c 8 := by
  obtain ⟨h1, h2⟩ := h
  apply rd_wr_other <;> bv_decide

/-- What the session writes before its work leaves the door's count alone. -/
theorem work_keeps {u c : Cell} (h : Outside u c) (m : Mem) (v : Cell) :
    rd (wr (wr (wr (wr (wr m (424#64 + u) 8 0#64) (440#64 + u) 8 (wordAddr "end-session")) (u + 8#64) 8 0#64)
      u 8 10#64) (312#64 + u) 8 v) c 8 = rd m c 8 := by
  rw [rd_wr_user h _ _ _ (by decide), rd_wr_user0 h, rd_wr_user' h _ _ _ (by decide),
    rd_wr_user h _ _ _ (by decide), rd_wr_user h _ _ _ (by decide)]

/-- And so does what it writes after, putting the terminal and `'bye` back. -/
theorem cleanup_keeps {u c : Cell} (h : Outside u c) (m : Mem) (v : Cell) :
    rd (wr (wr (wr (wr (wr (wr m (336#64 + u) 8 0#64) (144#64 + u) 8 (wordAddr "console-type"))
      (152#64 + u) 8 (wordAddr "console-key")) (160#64 + u) 8 (wordAddr "console-key?"))
      (312#64 + u) 8 0#64) (440#64 + u) 8 v) c 8 = rd m c 8 := by
  rw [rd_wr_user h _ _ _ (by decide), rd_wr_user h _ _ _ (by decide), rd_wr_user h _ _ _ (by decide),
    rd_wr_user h _ _ _ (by decide), rd_wr_user h _ _ _ (by decide), rd_wr_user h _ _ _ (by decide)]

theorem add_ones (x : Cell) : x + 18446744073709551615#64 = x - 1#64 := by bv_omega

/-- The rest of a session, from its CLOSE-CONNECTION. -/
theorem session_rest :
    Words.«session».code.drop 43 = [.call Words.«close-connection», .call Words.«tidy-session», .exit] := rfl

/-- The state when the session's work starts. -/
noncomputable abbrev atWork (door conn : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat) : S :=
  let m1 := wr (wr (wr (wr m (424 + u) 8 0) (440 + u) 8 (wordAddr "end-session")) (u + 8) 8 0) u 8 10
  ⟨rd m (door + 8) 8 :: conn :: s, rd m (440 + u) 8 :: door :: conn :: r,
   wr m1 (312 + u) 8 (rd m1 (wordAddr "session-idle" + 8) 8), u, e⟩

/-- The state when FAREWELL starts, after the work threw n. -/
noncomputable abbrev atFarewell (n door conn : Cell) (s r : List Cell) (m : Mem) (u : Cell) (f : Fail) : S :=
  ⟨n :: (List.range (s.length + 1 + 1)).map (junk f.ext), rd m (440 + u) 8 :: door :: conn :: r, f.mem, u, f.ext⟩

/-- However the session's work ends, unless it never does or ends the run,
SESSION comes to CLOSE-CONNECTION (`session_rest`) with the connection on
top, the caller's return stack, and one place fewer taken at the door. -/
theorem session_closes (conn door : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hout : Outside u (door + 24))
    (hw : Keeps (wordAddr "(session)") (door + 24))
    (hf : Keeps (wordAddr "farewell") (door + 24)) :
    (∃ st : S, st.ds.head? = some conn ∧ st.rs = r ∧ st.up = u ∧
       rd st.mem (door + 24) 8 = rd m (door + 24) 8 - 1 ∧
       Words.«session» ⟨door :: conn :: s, r, m, u, e⟩ =
         thread [.call Words.«close-connection», .call Words.«tidy-session», .exit] st)
    ∨ (∃ f : Fail, f.err.code = none ∧ Words.«session» ⟨door :: conn :: s, r, m, u, e⟩ = .error f) := by
  have hout' : Outside u (door + 24#64) := hout
  have hk := hw (atWork door conn s r m u e)
  simp only [Words.«session», Words.«session».code, thread]
  generalize Words.«close-connection» = cc
  generalize Words.«tidy-session» = ts
  cases hd : dispatch (wordAddr "(session)") (atWork door conn s r m u e) with
  | ok st =>
    rw [hd] at hk
    obtain ⟨ds, rs, mem, up, ext⟩ := st
    obtain ⟨hc, hrs, hup⟩ := hk
    simp only [atWork, BitVec.ofNat_eq_ofNat] at hd hc hrs hup
    subst hrs hup
    set_option simprocs false in
    simp only [forth, BitVec.add_zero, hd, List.getElem?_cons_zero, List.getElem?_cons_succ, List.length_cons,
      List.length_nil, ite_true, ite_false, if_pos, BitVec.ofNat_eq_ofNat]
    left
    refine ⟨⟨conn :: _, r, _, up, _⟩, rfl, rfl, rfl, ?_, rfl⟩
    rw [rd_wr_same, cleanup_keeps hout', hc, work_keeps hout', add_ones]
  | error f =>
    rw [hd] at hk
    simp only [atWork, BitVec.ofNat_eq_ofNat] at hd hk
    set_option simprocs false in
    simp only [forth, BitVec.add_zero, hd, List.getElem?_cons_zero, List.getElem?_cons_succ, List.length_cons,
      List.length_nil, ite_true, ite_false, if_pos, BitVec.ofNat_eq_ofNat]
    cases hn : f.err.code with
    | none => right; exact ⟨f, hn, by simp [hn]⟩
    | some n =>
      by_cases h0 : n = 0#64
      · subst h0
        simp only [hn]
        left
        refine ⟨⟨conn :: _, r, _, u, _⟩, rfl, rfl, rfl, ?_, rfl⟩
        rw [rd_wr_same, cleanup_keeps hout', hk, work_keeps hout', add_ones]
      · have hk2 := hf (atFarewell n door conn s r m u f)
        simp only [hn, h0, ite_false]
        cases hd2 : dispatch (wordAddr "farewell") (atFarewell n door conn s r m u f) with
        | ok st =>
          rw [hd2] at hk2
          obtain ⟨ds, rs, mem, up, ext⟩ := st
          obtain ⟨hc, hrs, hup⟩ := hk2
          simp only [atFarewell, BitVec.ofNat_eq_ofNat] at hd2 hc hrs hup
          subst hrs hup
          simp only [hd2, ite_true]
          left
          refine ⟨⟨conn :: _, r, _, up, _⟩, rfl, rfl, rfl, ?_, rfl⟩
          rw [rd_wr_same, cleanup_keeps hout', hc, hk, work_keeps hout', add_ones]
        | error f2 =>
          rw [hd2] at hk2
          simp only [atFarewell, BitVec.ofNat_eq_ofNat] at hd2 hk2
          simp only [hd2]
          cases hn2 : f2.err.code with
          | none => right; exact ⟨f2, hn2, by simp [hn2]⟩
          | some k =>
            left
            by_cases hk0 : k = 0#64
            · subst hk0
              simp only [hn2, ite_true]
              refine ⟨⟨conn :: _, r, _, u, _⟩, rfl, rfl, rfl, ?_, rfl⟩
              rw [rd_wr_same, cleanup_keeps hout', hk2, hk, work_keeps hout', add_ones]
            · simp [hn2, hk0, List.range_succ_eq_map]
              refine ⟨⟨conn :: _, r, _, u, _⟩, rfl, rfl, rfl, ?_, rfl⟩
              rw [rd_wr_same, cleanup_keeps hout', hk2, hk, work_keeps hout', add_ones]

/-- A connection's task runs SESSION with the door it came in by. -/
theorem run_session_wired :
    Words.«run-session».code = [.call Prim.dup, .call Words.«door-of», .call Words.«session», .exit] := rfl

end OS4.Sessions

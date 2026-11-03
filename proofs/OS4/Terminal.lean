import OS4.Printing
import OS4.Words.NetRepl
import OS4.Words.NetTelnet

/-!
# The sandbox's terminal (V2)

`isolated_given_terminal` assumed that the task's `type` and `bye` keep the
setting. They run whatever its vectors `'type` and `'bye` hold, which are in
the support (`Box.userSupp`), so no sandbox word can change them. What they
hold is part of the setting (`Box.Term`): the console's `console-type` and the
kernel's BYE, or a network session's `telnet-type` and `end-session`
(net/telnet.fs, net/repl.fs).

Here `type` and `bye` are proven to keep the setting for each of those, but
`telnet-type`, which sends through the connection, is a hypothesis; it is
proven in `Telnet.lean`, which gives the whole result (`isolated`).
-/

namespace OS4.Isolation
open OS4

/-- What the task's terminal vectors run when INTERPRET starts. That an xt
runs the word named is the dumper's word, as for `hdump`. -/
structure Box.Term (B : Box) : Prop where
  type : dispatch (rd B.m0 (B.p + 144) 8) = Words.«console-type» ∨
    dispatch (rd B.m0 (B.p + 144) 8) = Words.«telnet-type»
  bye : dispatch (rd B.m0 (B.p + 440) 8) = Prim.bye ∨
    dispatch (rd B.m0 (B.p + 440) 8) = Words.«end-session»

section
variable {B : Box}

/-! ## The vectored words: run the xt in their cell -/

theorem type_ok (s s' : S) (h : Words.«type» s = .ok s') :
    dispatch (rd s.mem (s.up + 144) 8) s = .ok s' := by
  rcases s with ⟨ds, rs, m, u, e⟩
  simp only [Words.«type», Words.«type».code, Words.«'type», Words.«'type».code, thread, run, forth,
    List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil] at h
  rw [BitVec.add_comm 144 u] at h
  split at h <;> simp_all

theorem bye_ok (s s' : S) (h : Words.«bye#2» s = .ok s') :
    dispatch (rd s.mem (s.up + 440) 8) s = .ok s' := by
  rcases s with ⟨ds, rs, m, u, e⟩
  simp only [Words.«bye#2», Words.«bye#2».code, Words.«'bye», Words.«'bye».code, thread, run, forth,
    List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil] at h
  rw [BitVec.add_comm 440 u] at h
  split at h <;> simp_all

/-! ## The words the vectors may hold -/

theorem emit_frame (W) : Frame W Prim.emit := by frame_prim

theorem console_type_frame (W) : Frame W Words.«console-type» :=
  loopThread_frame (by simp only [Words.«console-type».code]
                       frames [Prim.dup_frame, Prim.cfetch_frame, emit_frame, oneplus_frame,
                         Prim.drop_frame])

theorem eof_frame (W) : Frame W Words.«eof» := uvar_frame rfl W

/-- `end-session`: store true in `eof`, which the support misses. -/
theorem end_session_keeps (hB : B.Ok) : B.Keeps Words.«end-session» := by
  refine (thread_keeps_at (F := fun pc s => pc = 2 → ∃ t, s.ds = (B.p + 424) :: t)
    (fun _ h => absurd h (by decide)) ?_).1
  simp only [Words.«end-session».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨gk (nk (pushConst_frame _ _)) (fun _ _ _ _ _ _ h => absurd h (by decide)),
    gk (nk (eof_frame _)) fun s s' hu _ _ h _ => ?_,
    gs store_at (Box.supp_apart hB (by decide)) (fun s h => h rfl) (fun _ h => absurd h (by decide)), ge⟩
  rw [uvar_ok rfl s s' h, hu]
  exact ⟨s.ds, rfl⟩

/-- The kernel's BYE ends the run, so never returns. -/
theorem kbye_keeps : B.Keeps Prim.bye := by
  intro s s' _ _ h
  simp [Prim.bye, S.fail] at h

/-! ## TYPE and BYE -/

theorem type_keeps (hT : B.Term) (htt : B.Keeps Words.«telnet-type») : B.Keeps Words.«type» := by
  intro s s' hu hI h
  have hd := type_ok s s' h
  rw [hu, B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inr (by bv_omega))] at hd
  rcases hT.type with h1 | h1 <;> rw [h1] at hd
  · exact nk (console_type_frame _) s s' hu hI hd
  · exact htt s s' hu hI hd

theorem bye_keeps (hB : B.Ok) (hT : B.Term) : B.Keeps Words.«bye#2» := by
  intro s s' hu hI h
  have hd := bye_ok s s' h
  rw [hu, B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inr (by bv_omega))] at hd
  rcases hT.bye with h1 | h1 <;> rw [h1] at hd
  · exact kbye_keeps s s' hu hI hd
  · exact end_session_keeps hB s s' hu hI hd

end

/-- **Sandbox isolation, given the connection's output.** A task whose search
order is the sandbox alone, on the console or a network session, executes
only the sandbox's words, for any line. Assumed: the dump's headers
(`hdump`), and that `telnet-type` keeps the setting. -/
theorem isolated_given_telnet (B : Box) (hB : B.Ok) (hT : B.Term)
    (hdump : ∀ h ∈ B.hs, ∃ f ∈ Words.«sandbox-wordlist».words, dispatch (Box.xtOf B.m0 h) = f)
    (htt : B.Keeps Words.«telnet-type»)
    (d : Cell → Sem) (hd : ∀ xt, B.Allowed xt → d xt = dispatch xt)
    (s : S) (hu : s.up = B.p) (hm : s.mem = B.m0) :
    loopThread (Words.«interpret».code.set 29 (.call (execWith d))) s = Words.«interpret» s :=
  isolated_given_terminal B hB hdump (type_keeps hT htt) (bye_keeps hB hT) d hd s hu hm

end OS4.Isolation

import OS4.Terminal
import OS4.Foots.NetTelnet

/-!
# The connection's output (V2)

`isolated_given_telnet` assumed that `telnet-type` keeps the setting. It
sends through the session's connection (`term-conn`): it writes the
connection's record, the frames it builds and the network's variables, and it
pauses. Here it is proven to keep the setting, given what a session rests on
(`Box.Net`): other tasks and devices leave the setting and the task's
`cur-conn` alone, and the connection's record and what TCP output writes for
it miss them.

The words it runs are proven one instruction at a time (`GQ`), as INTERPRET
is: what they write is known from frames and footprints, and the stack facts
that matter (the address of a store, the connection on top for TCP output)
are tracked where they are needed. After a failed wait, `(send)` resets the
connection and throws again; from there it never returns, so what it writes
on the way does not matter (`D`, the points that only lead to a failure).
-/

namespace OS4.Isolation
open OS4

/-! ## What a session's terminal rests on -/

/-- The connection a network session's terminal sends on: its `term-conn`,
which is part of the setting. -/
def Box.conn (B : Box) : Cell := rd B.m0 (B.p + 336) 8

/-- The bytes a sending word leaves alone: the setting's, and the task's
`cur-conn`, which says which connection SEND works on. -/
def Box.prot (B : Box) (a : Cell) : Prop := B.supp a ∨ (a - (B.p + 328)).toNat < 8

/-- What the session's terminal rests on: no other task or device writes the
protected bytes; the connection's record (`/conn`, 12464 bytes) misses them;
and so does everything TCP output writes for the connection (its generated
footprint: the frames and the network's variables). -/
structure Box.Net (B : Box) : Prop where
  quiet : ∀ a, B.prot a → Quiet a
  apart : ∀ a, B.prot a → 12464 ≤ (a - B.conn).toNat
  out : ∀ a, B.prot a → ¬ Writes Words.«tcp-output».regs ⟨[B.conn], [], B.p⟩ a

/-- f, run in B's user area from a state where pre holds, returns with the
same user area and P's bytes as they were. -/
def Box.Guards (B : Box) (P : Cell → Prop) (pre : S → Prop) (f : Sem) : Prop :=
  ∀ s s', s.up = B.p → pre s → f s = .ok s' → s'.up = B.p ∧ ∀ a, P a → s'.mem a = s.mem a

/-- `cur-conn` holds the session's connection. -/
def OnConn (B : Box) (s : S) : Prop := rd s.mem (B.p + 328) 8 = B.conn

/-! ## The invariant, one instruction at a time -/

/-- B's user area, and P's bytes as in s0. -/
def Nm (B : Box) (P : Cell → Prop) (s0 s : S) : Prop :=
  s.up = B.p ∧ ∀ a, P a → s.mem a = s0.mem a

/-- `Nm` except at the points D, from which the thread only fails; and what R
knows. -/
def GQ (B : Box) (P : Cell → Prop) (s0 : S) (D : List Nat) (R : Nat → S → Prop) (pc : Nat) (s : S) :
    Prop :=
  (pc ∉ D → Nm B P s0 s) ∧ R pc s

/-- A thread whose every instruction keeps `GQ` guards P. -/
theorem guards_of {B : Box} {P : Cell → Prop} {code : List Ins} {pre : S → Prop} {D : List Nat}
    {R : S → Nat → S → Prop} (hexit : ∀ pc, code[pc]? = some .exit → pc ∉ D)
    (h0 : ∀ s, pre s → R s 0 s)
    (h : ∀ s0, s0.up = B.p → pre s0 → ∀ pc i, code[pc]? = some i → Keeps (GQ B P s0 D (R s0)) pc i) :
    B.Guards P pre (thread code) ∧ B.Guards P pre (loopThread code) := by
  have go : ∀ n s s', s.up = B.p → pre s → run code n 0 s = .ok s' →
      s'.up = B.p ∧ ∀ a, P a → s'.mem a = s.mem a := by
    intro n s s' hu hp hs
    obtain ⟨pe, hpe, hq, _⟩ := run_inv code _ (invariant_of_keeps (h s hu hp)) n 0 s s'
      ⟨fun _ => ⟨hu, fun _ _ => rfl⟩, h0 s hp⟩ hs
    exact hq (hexit pe hpe)
  refine ⟨fun s s' hu hp hs => go _ s s' hu hp hs, fun s s' hu hp hs => ?_⟩
  unfold loopThread at hs
  split at hs
  · exact go _ s s' hu hp hs
  · simp [S.fail] at hs

/-- What a footprint says of the stack below a word's inputs. -/
theorem foot_drop {f : Sem} {k j : Nat} {regs : List Reg} {dout : List Val}
    (hf : Foot f k j 0 0 regs dout []) {s s' : S} (hk : k ≤ s.ds.length) (h : f s = .ok s') :
    s'.ds.drop j = s.ds.drop k ∧ s'.up = s.up := by
  rcases s with ⟨ds, rs, m, u, e⟩
  have hft := (hf (ds.take k) [] (ds.drop k) rs m u e
    (by rw [List.length_take]; exact Nat.min_eq_left hk) rfl).2
  simp only [List.take_append_drop, List.nil_append, h, FOut] at hft
  exact ⟨hft.2.1, hft.2.2.2.2.2.2⟩

/-- Outside regions whose bases and lengths are known. -/
theorem not_writes {regs : List Reg} {ρ : Env} {a : Cell}
    (h : ∀ r ∈ regs, ∃ b l, r.base.eval ρ = some b ∧ r.len.eval ρ = some l ∧ l.toNat ≤ (a - b).toNat) :
    ¬ Writes regs ρ a := by
  rintro ⟨r, hr, hh⟩
  obtain ⟨b, l, hb, hl, h'⟩ := h r hr
  have := hh b l hb hl
  omega

/-- The protected bytes miss a user variable between the setting's cells and
apart from `cur-conn`. -/
theorem Box.prot_user {B : Box} (hB : B.Ok) {off : Cell}
    (h : (16 ≤ off.toNat ∧ off.toNat + 8 ≤ 144) ∨ (152 ≤ off.toNat ∧ off.toNat + 8 ≤ 176) ∨
      (184 ≤ off.toNat ∧ off.toNat + 8 ≤ 328)) :
    ∀ a, B.prot a → 8 ≤ (a - (B.p + off)).toNat := by
  intro a ha
  rcases ha with ha | ha
  · exact Box.supp_apart hB (by omega) a ha
  · bv_omega

section
variable {B : Box} {P : Cell → Prop} {s0 : S} {D : List Nat} {R : Nat → S → Prop} {pc : Nat}

theorem hc {f : Sem} (hD : pc ∉ D)
    (hf : ∀ s s', Nm B P s0 s → R pc s → f s = .ok s' → Nm B P s0 s' ∧ R (pc + 1) s') :
    Keeps (GQ B P s0 D R) pc (.call f) := by
  intro s pc' s' ⟨hn, hr⟩ hs
  cases hs with
  | call h =>
    obtain ⟨h1, h2⟩ := hf s s' (hn hD) hr h
    exact ⟨fun _ => h1, h2⟩

/-- A call with a frame that misses P. -/
theorem hfr {f : Sem} {W : Cell → Cell → Prop} (hf : Frame W f) (hW : ∀ a, P a → ¬ W B.p a) (hD : pc ∉ D)
    (hR : ∀ s s', Nm B P s0 s → R pc s → f s = .ok s' → (∀ a, ¬ W B.p a → s'.mem a = s.mem a) →
      R (pc + 1) s') :
    Keeps (GQ B P s0 D R) pc (.call f) :=
  hc hD fun s s' hn hr h => by
    obtain ⟨hu', hm⟩ := hf s s' h
    have hm' : ∀ a, ¬ W B.p a → s'.mem a = s.mem a := fun a ha => hm a (by rw [hn.1]; exact ha)
    exact ⟨⟨hu'.trans hn.1, fun a ha => (hm' a (hW a ha)).trans (hn.2 a ha)⟩, hR s s' hn hr h hm'⟩

/-- A call of a word that writes nothing. -/
theorem hn {f : Sem} (hf : Frame noCell f) (hD : pc ∉ D)
    (hR : ∀ s s', Nm B P s0 s → R pc s → f s = .ok s' → s'.mem = s.mem → R (pc + 1) s') :
    Keeps (GQ B P s0 D R) pc (.call f) :=
  hfr hf (fun _ _ h => h) hD fun s s' hn hr h hm => hR s s' hn hr h (funext fun a => hm a id)

/-- A call with a footprint whose regions, given the stack, miss P. -/
theorem hft {f : Sem} {k j : Nat} {regs : List Reg} {dout : List Val} (hf : Foot f k j 0 0 regs dout [])
    (hq : ∀ a, P a → Quiet a) (hD : pc ∉ D)
    (hpre : ∀ s, Nm B P s0 s → R pc s → k ≤ s.ds.length ∧ ∀ a, P a → ¬ Writes regs ⟨s.ds.take k, [], B.p⟩ a)
    (hR : ∀ s s', Nm B P s0 s → R pc s → f s = .ok s' → s'.ds.drop j = s.ds.drop k →
      (∀ a, P a → s'.mem a = s.mem a) → R (pc + 1) s') :
    Keeps (GQ B P s0 D R) pc (.call f) :=
  hc hD fun s s' hn hr h => by
    obtain ⟨hk, hw⟩ := hpre s hn hr
    obtain ⟨hdrop, hup⟩ := foot_drop hf hk h
    rcases s with ⟨ds, rs, m, u, e⟩
    obtain ⟨hu, hm0⟩ := hn
    simp only at hu hk hw hm0 hdrop hup
    subst hu
    have hft := (hf (ds.take k) [] (ds.drop k) rs m B.p e
      (by rw [List.length_take]; exact Nat.min_eq_left hk) rfl).1
    simp only [List.take_append_drop, List.nil_append, h, resMem] at hft
    have hm : ∀ a, P a → s'.mem a = m a := fun a ha => hft a (hq a ha) (hw a ha)
    exact ⟨⟨hup, fun a ha => (hm a ha).trans (hm0 a ha)⟩, hR _ s' ⟨rfl, hm0⟩ hr h hdrop hm⟩

/-- A call that P's guard covers. -/
theorem hg {f : Sem} {P' : Cell → Prop} {pre : S → Prop} (hgd : B.Guards P' pre f) (hP : ∀ a, P a → P' a)
    (hD : pc ∉ D) (hpre : ∀ s, Nm B P s0 s → R pc s → pre s)
    (hR : ∀ s s', Nm B P s0 s → R pc s → f s = .ok s' → (∀ a, P' a → s'.mem a = s.mem a) →
      R (pc + 1) s') :
    Keeps (GQ B P s0 D R) pc (.call f) :=
  hc hD fun s s' hn hr h => by
    obtain ⟨hu', hm⟩ := hgd s s' hn.1 (hpre s hn hr) h
    exact ⟨⟨hu', fun a ha => (hm a (hP a ha)).trans (hn.2 a ha)⟩, hR s s' hn hr h hm⟩

/-- A call on the way to a failure. -/
theorem hcd {f : Sem} (hD : pc + 1 ∈ D) (hR : ∀ s s', R pc s → f s = .ok s' → R (pc + 1) s') :
    Keeps (GQ B P s0 D R) pc (.call f) := by
  intro s pc' s' ⟨_, hr⟩ hs
  cases hs with
  | call h => exact ⟨fun h' => absurd hD h', hR s s' hr h⟩

theorem hl {v : Cell} (hD : pc + 1 ∉ D → pc ∉ D) (hR : ∀ s, R pc s → R (pc + 1) { s with ds := v :: s.ds }) :
    Keeps (GQ B P s0 D R) pc (.lit v) := by
  intro s pc' s' ⟨hm, hr⟩ hs
  cases hs with
  | lit => exact ⟨fun h => hm (hD h), hR _ hr⟩

theorem hb {t : Nat} (hD : t ∉ D → pc ∉ D) (hR : ∀ s, R pc s → R t s) :
    Keeps (GQ B P s0 D R) pc (.branch t) := by
  intro s pc' s' ⟨hm, hr⟩ hs
  cases hs with
  | branch => exact ⟨fun h => hm (hD h), hR _ hr⟩

theorem hz {t : Nat} (hD : pc ∉ D)
    (hj : ∀ s ds, s.ds = 0 :: ds → R pc s → R t { s with ds := ds })
    (hf : ∀ s x ds, s.ds = x :: ds → x ≠ 0 → R pc s → R (pc + 1) { s with ds := ds }) :
    Keeps (GQ B P s0 D R) pc (.zbranch t) := by
  intro s pc' s' ⟨hm, hr⟩ hs
  cases hs with
  | zjump hds => exact ⟨fun _ => hm hD, hj _ _ hds hr⟩
  | zfall hds hx => exact ⟨fun _ => hm hD, hf _ _ _ hds hx hr⟩

theorem hq {t : Nat} (hD : pc ∉ D) (h1 : ∀ s, R t s) (h2 : ∀ s, R (pc + 1) s) :
    Keeps (GQ B P s0 D R) pc (.qdo t) := by
  intro s pc' s' ⟨hm, _⟩ hs
  cases hs with
  | qdoSkip => exact ⟨fun _ => hm hD, h1 _⟩
  | qdoEnter => exact ⟨fun _ => hm hD, h2 _⟩

theorem hlp {t : Nat} (hD : pc ∉ D) (h1 : ∀ s, R t s) (h2 : ∀ s, R (pc + 1) s) :
    Keeps (GQ B P s0 D R) pc (.loop t) := by
  intro s pc' s' ⟨hm, _⟩ hs
  cases hs with
  | loopEnd => exact ⟨fun _ => hm hD, h2 _⟩
  | loopBack => exact ⟨fun _ => hm hD, h1 _⟩

theorem he : Keeps (GQ B P s0 D R) pc .exit := by
  intro s pc' s' _ hs
  cases hs

end

/-! ## Words that write nothing -/

theorem field_frame {code : List Ins} {n : Cell} (hc : code = [.lit n, .call Prim.plus, .exit]) (W) :
    Frame W (thread code) := by
  subst hc
  exact thread_frame (by frames [Prim.plus_frame])

theorem field_ok {code : List Ins} {n : Cell} (hc : code = [.lit n, .call Prim.plus, .exit]) (s s' : S)
    (h : thread code s = .ok s') : ∃ x t, s.ds = x :: t ∧ s' = { s with ds := (x + n) :: t } := by
  subst hc
  rcases s with ⟨_ | ⟨x, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp only [forth] at h
    cases h
    exact ⟨x, t, rfl, rfl⟩

theorem Prim.unloop_frame (W) : Frame W Prim.unloop := by
  intro s s' h
  rcases s with ⟨ds, _ | ⟨a, _ | ⟨b, rs⟩⟩, m, u, e⟩ <;> simp [forth, S.fail] at h
  cases h
  exact ⟨rfl, fun _ _ => rfl⟩

section
variable (W : Cell → Cell → Prop)
theorem cflags_frame : Frame W Words.«c.flags» := field_frame rfl W
theorem cstate_frame : Frame W Words.«c.state» := field_frame rfl W
theorem ctxq_frame : Frame W Words.«c.tx-queued» := field_frame rfl W
theorem ctxa_frame : Frame W Words.«c.tx-acked» := field_frame rfl W
theorem ctxs_frame : Frame W Words.«c.tx-sent» := field_frame rfl W
theorem ctx_frame : Frame W Words.«c.tx» := field_frame rfl W
theorem established_frame : Frame W Words.«established» := pushConst_frame _ W
theorem close_wait_frame : Frame W Words.«close-wait» := pushConst_frame _ W
theorem fin_queued_frame : Frame W Words.«fin-queued» := pushConst_frame _ W
theorem slash_tx_frame : Frame W Words.«/tx» := pushConst_frame _ W
theorem iac_frame : Frame W Words.«iac» := pushConst_frame _ W
theorem flag_frame : Frame W Words.«flag?» :=
  thread_frame (by simp only [Words.«flag?».code]
                   frames [Prim.swap_frame, cflags_frame, Prim.fetch_frame, Prim.and_frame, zne_frame])
theorem open_frame : Frame W Words.«open?» :=
  thread_frame (by simp only [Words.«open?».code]
                   frames [Prim.dup_frame, cstate_frame, Prim.fetch_frame, established_frame,
                     Prim.equal_frame, Prim.swap_frame, close_wait_frame, Prim.or_frame, fin_queued_frame,
                     flag_frame, Prim.zequal_frame, Prim.and_frame])
theorem tx_room_frame : Frame W Words.«tx-room» :=
  thread_frame (by simp only [Words.«tx-room».code]
                   frames [Prim.dup_frame, ctxq_frame, Prim.fetch_frame, Prim.swap_frame, ctxa_frame,
                     Prim.minus_frame, slash_tx_frame])
theorem in_flight_frame : Frame W Words.«in-flight» :=
  thread_frame (by simp only [Words.«in-flight».code]
                   frames [Prim.dup_frame, ctxs_frame, Prim.fetch_frame, Prim.swap_frame, ctxa_frame,
                     Prim.minus_frame])
theorem special_frame : Frame W Words.«special?» :=
  thread_frame (by simp only [Words.«special?».code]
                   frames [Prim.dup_frame, Prim.equal_frame, Prim.swap_frame, iac_frame, Prim.or_frame])
theorem plain_frame : Frame W Words.«plain» :=
  loopThread_frame (by simp only [Words.«plain».code]
                       frames [tuck_frame, Prim.dup_frame, i_frame, Prim.plus_frame, Prim.cfetch_frame,
                         special_frame, twodrop_frame, Prim.unloop_frame, Prim.drop_frame])
end

/-! ## `io-wait` -/

section
variable {B : Box}

/-- What `io-wait` needs of its stack: the owner cell's address for its
store, a count for `stop-until`, and the code it throws. -/
def ioR (B : Box) : Nat → S → Prop
  | 1, s => ∃ t, s.ds = B.p :: t
  | 2, s => ∃ t, s.ds = (B.p + 328) :: B.p :: t
  | 3, s => ∃ t, s.ds = B.conn :: B.p :: t
  | 4, s => ∃ t, s.ds = (B.conn + 160) :: B.p :: t
  | 8, s => (∃ t, s.ds = 0 :: t) ∨ ∃ x t, s.ds = x :: x :: t
  | 9, s => ∃ x t, s.ds = x :: t
  | 10, s => ∃ x t, s.ds = x :: x :: t
  | 11, s => ∃ f x t, s.ds = f :: x :: t
  | 14, s => ∃ t, s.ds = 18446744073709551343 :: t
  | 15, s => ∃ x t, s.ds = x :: t
  | _, _ => True

theorem onConn_of {s0 s : S} (hp : OnConn B s0) (hn : Nm B B.prot s0 s) : rd s.mem (B.p + 328) 8 = B.conn := by
  rw [rd_congr s.mem s0.mem 8 _ fun i hi => hn.2 _ (Or.inr (by bv_omega))]
  exact hp

/-- `io-wait`: mark the connection as this task's, then sleep. -/
theorem io_wait_guards (hB : B.Ok) (hN : B.Net) : B.Guards B.prot (OnConn B) Words.«io-wait» := by
  refine (guards_of (D := []) (R := fun _ => ioR B) (fun _ _ => List.not_mem_nil)
    (fun _ _ => trivial) fun s0 _ hp0 => ?_).1
  simp only [Words.«io-wait».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he⟩
  · exact hn (Prim.upfetch_frame _) List.not_mem_nil fun s s' hn _ h _ => by
      simp only [forth] at h; cases h; exact ⟨s.ds, by rw [hn.1]⟩
  · exact hn (uvar_frame rfl _) List.not_mem_nil fun s s' hn hr h _ => by
      obtain ⟨t, ht⟩ := hr
      rw [uvar_ok rfl s s' h]
      exact ⟨t, by simp only [ht, hn.1]⟩
  · exact hn (Prim.fetch_frame _) List.not_mem_nil fun s s' hn hr h _ => by
      obtain ⟨t, ht⟩ := hr
      have hc := onConn_of hp0 hn
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht hc
      subst ht
      simp only [forth] at h
      cases h
      exact ⟨t, by rw [hc]⟩
  · exact hn (field_frame rfl _) List.not_mem_nil fun s s' _ hr h _ => by
      obtain ⟨t, ht⟩ := hr
      obtain ⟨x, t', hx, rfl⟩ := field_ok rfl s s' h
      rw [ht] at hx
      cases hx
      exact ⟨t, rfl⟩
  · refine hft Prim.store_foot hN.quiet List.not_mem_nil (fun s _ hr => ?_) fun _ _ _ _ _ _ _ => trivial
    obtain ⟨t, ht⟩ := hr
    refine ⟨by simp [ht], fun a ha => not_writes ?_⟩
    simp only [ht, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    have := hN.apart a ha
    exact ⟨_, _, rfl, rfl, by simp; bv_omega⟩
  · exact hn (uvar_frame rfl _) List.not_mem_nil fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.fetch_frame _) List.not_mem_nil fun _ _ _ _ _ _ => trivial
  · exact hn (qdup_frame _) List.not_mem_nil fun s s' _ _ h _ => by
      obtain ⟨x, t, _, hds'⟩ := qdup_shape s s' h
      show (∃ t, s'.ds = 0 :: t) ∨ ∃ x t, s'.ds = x :: x :: t
      by_cases hx : x = 0
      · simp only [hx, if_true] at hds'; exact Or.inl ⟨t, hds'⟩
      · simp only [hx, if_false] at hds'; exact Or.inr ⟨x, t, hds'⟩
  · refine hz List.not_mem_nil (fun _ _ _ _ => trivial) fun s x ds hds hx hr => ?_
    rcases hr with ⟨t, ht⟩ | ⟨y, t, ht⟩
    · rw [ht, List.cons.injEq] at hds
      exact absurd hds.1.symm hx
    · rw [ht, List.cons.injEq] at hds
      exact ⟨y, t, hds.2.symm⟩
  · exact hn (Prim.dup_frame _) List.not_mem_nil fun s s' _ hr h _ => by
      obtain ⟨x, t, ht⟩ := hr
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht
      subst ht
      simp only [forth] at h
      cases h
      exact ⟨x, t, rfl⟩
  · refine hft Words.«expired?».foot hN.quiet List.not_mem_nil
      (fun s _ hr => ?_) fun s s' _ hr _ hd _ => ?_
    · obtain ⟨x, t, ht⟩ := hr
      exact ⟨by simp [ht], fun a _ => not_writes (by simp)⟩
    · obtain ⟨x, t, ht⟩ := hr
      rw [ht] at hd
      rcases hs' : s'.ds with _ | ⟨f, t'⟩
      · rw [hs'] at hd; simp at hd
      · rw [hs'] at hd
        simp only [List.drop_succ_cons, List.drop_zero] at hd
        exact ⟨f, x, t, by rw [hs', hd]⟩
  · refine hz List.not_mem_nil (fun s ds hds hr => ?_) fun _ _ _ _ _ _ => trivial
    obtain ⟨f, x, t, ht⟩ := hr
    rw [ht] at hds
    cases hds
    exact ⟨x, t, rfl⟩
  · exact hn (Prim.drop_frame _) List.not_mem_nil fun _ _ _ _ _ _ => trivial
  · exact hl (fun _ => List.not_mem_nil) fun s _ => ⟨s.ds, rfl⟩
  · exact hn (throwM_frame _) List.not_mem_nil fun s s' _ hr h _ => by
      obtain ⟨t, ht⟩ := hr
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht
      subst ht
      simp [forth] at h
  · refine hft Words.«stop-until».foot hN.quiet List.not_mem_nil (fun s _ hr => ?_)
      fun _ _ _ _ _ _ _ => trivial
    obtain ⟨x, t, ht⟩ := hr
    refine ⟨by simp [ht], fun a ha => not_writes ?_⟩
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨⟨_, _, rfl, rfl, by simpa using Box.prot_user hB (off := 72) (by decide) a ha⟩,
      ⟨_, _, rfl, rfl, by simpa using Box.prot_user hB (off := 64) (by decide) a ha⟩⟩
  · exact hb (fun _ => List.not_mem_nil) fun _ _ => trivial
  · refine hft Words.«stop».foot hN.quiet List.not_mem_nil (fun s _ _ => ?_)
      fun _ _ _ _ _ _ _ => trivial
    refine ⟨Nat.zero_le _, fun a ha => not_writes ?_⟩
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨⟨_, _, rfl, rfl, by simpa using Box.prot_user hB (off := 64) (by decide) a ha⟩,
      ⟨_, _, rfl, rfl, by simpa using Box.prot_user hB (off := 72) (by decide) a ha⟩⟩

end

/-! ## Steps on the stack -/

section
variable {s s' : S}

theorem fetch_ok (h : Prim.fetch s = .ok s') :
    ∃ a t, s.ds = a :: t ∧ s' = { s with ds := rd s.mem a 8 :: t } := by
  rcases s with ⟨_ | ⟨a, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp only [forth] at h; cases h; exact ⟨a, t, rfl, rfl⟩

theorem cfetch_ok (h : Prim.cfetch s = .ok s') : ∃ a t, s.ds = a :: t ∧ s' = { s with ds := rd s.mem a 1 :: t } := by
  rcases s with ⟨_ | ⟨a, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp only [forth] at h; cases h; exact ⟨a, t, rfl, rfl⟩

theorem dup_ok (h : Prim.dup s = .ok s') : ∃ x t, s.ds = x :: t ∧ s' = { s with ds := x :: x :: t } := by
  rcases s with ⟨_ | ⟨x, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp only [forth] at h; cases h; exact ⟨x, t, rfl, rfl⟩

theorem bin_ok {f : Cell → Cell → Cell} (h : Prim.bin f s = .ok s') :
    ∃ b a t, s.ds = b :: a :: t ∧ s' = { s with ds := f a b :: t } := by
  rcases s with ⟨_ | ⟨b, _ | ⟨a, t⟩⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp [forth, S.fail] at h
  · simp only [forth] at h; cases h; exact ⟨b, a, t, rfl, rfl⟩

theorem i_ok (h : Prim.i s = .ok s') : ∃ x, s' = { s with ds := x :: s.ds } := by
  rcases s with ⟨ds, _ | ⟨x, rs⟩, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp only [forth] at h; cases h; exact ⟨x, rfl⟩

theorem pushConst_ok {v : Cell} (h : pushConst v s = .ok s') : s' = { s with ds := v :: s.ds } := by
  simp only [pushConst] at h; cases h; rfl

theorem oneminus_ok (h : Words.«1-» s = .ok s') : ∃ x t, s.ds = x :: t ∧ s' = { s with ds := (x - 1) :: t } := by
  rcases s with ⟨_ | ⟨x, t⟩, rs, m, u, e⟩
  · simp [forth, S.fail] at h
  · simp only [forth] at h; cases h; exact ⟨x, t, rfl, rfl⟩

end

/-! ## `(send)` -/

section
variable {B : Box}

/-- What `(send)` needs of its stack: the connection on top for TCP output
and its parts; the ring offset under its mask for the store into the
transmit ring; the code after a failed wait, which it throws again. -/
def sendR (B : Box) (s0 : S) : Nat → S → Prop
  | 10, s => ∃ t, s.ds = 18446744073709551347 :: t
  | 18, s => ∃ t, s.ds = (B.p + 328) :: t
  | 19, s => ∃ t, s.ds = B.conn :: t
  | 21, s => ∃ t, s.ds = wordAddr "io-wait" :: t
  | 22, s => (∃ t, s.ds = 0 :: t ∧ Nm B B.prot s0 s) ∨ ∃ x t, s.ds = x :: t ∧ x ≠ 0
  | 23, s => (∃ t, s.ds = 0 :: t ∧ Nm B B.prot s0 s) ∨ ∃ x t, s.ds = x :: x :: t ∧ x ≠ 0
  | 24, s => ∃ x t, s.ds = x :: t ∧ x ≠ 0
  | 25, s => ∃ y x t, s.ds = y :: x :: t ∧ x ≠ 0
  | 26, s => ∃ y x t, s.ds = y :: x :: t ∧ x ≠ 0
  | 27, s => ∃ x t, s.ds = x :: t ∧ x ≠ 0
  | 40, s => ∃ w t, s.ds = w :: t
  | 41, s => ∃ x w t, s.ds = x :: w :: t
  | 42, s => ∃ x w t, s.ds = x :: w :: t
  | 43, s => ∃ x w t, s.ds = x :: w :: t
  | 44, s => ∃ x w t, s.ds = x :: w :: t
  | 45, s => ∃ i x w t, s.ds = i :: x :: w :: t
  | 46, s => ∃ z w t, s.ds = z :: w :: t
  | 47, s => ∃ z w t, s.ds = 8192 :: z :: w :: t
  | 48, s => ∃ z w t, s.ds = (8192 - 1) :: z :: w :: t
  | 49, s => ∃ y w t, s.ds = y :: w :: t ∧ y.toNat < 8192
  | 50, s => ∃ y w t, s.ds = (B.p + 328) :: y :: w :: t ∧ y.toNat < 8192
  | 51, s => ∃ y w t, s.ds = B.conn :: y :: w :: t ∧ y.toNat < 8192
  | 52, s => ∃ y w t, s.ds = (B.conn + 4272) :: y :: w :: t ∧ y.toNat < 8192
  | 53, s => ∃ y w t, s.ds = (y + (B.conn + 4272)) :: w :: t ∧ y.toNat < 8192
  | 56, s => ∃ x t, s.ds = x :: t
  | 57, s => ∃ x t, s.ds = (B.p + 328) :: x :: t
  | 58, s => ∃ x t, s.ds = B.conn :: x :: t
  | 59, s => ∃ x t, s.ds = (B.conn + 72) :: x :: t
  | _, _ => True

/-- After a failed wait: reset the connection, throw again. -/
abbrev sendD : List Nat := [22, 23, 24, 25, 26, 27]

/-- `(send)`: queue the data in the connection's transmit ring, waiting for
room; it writes only the connection's record, its own `io-until`, and what
TCP output and the wait write. -/
theorem send_guards (hB : B.Ok) (hN : B.Net) [Runs "(arp-request)" Words.«(arp-request)»]
    [Runs "(segment-out)" Words.«(segment-out)»] [Runs "(tcp-output)" Words.«(tcp-output)»]
    [Runs "(free-conn)" Words.«(free-conn)»] [Runs "io-wait" Words.«io-wait»] :
    B.Guards B.prot (OnConn B) Words.«(send)» := by
  refine (guards_of (D := sendD) (R := sendR B) ?_ (fun _ _ => trivial) fun s0 _ hp0 => ?_).2
  · intro pc hpc hD
    simp only [sendD, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Words.«(send)».code] at hpc
  simp only [Words.«(send)».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, he⟩
  -- 0: io-start
  · refine hft Words.«io-start».foot hN.quiet (by decide)
      (fun s _ _ => ⟨Nat.zero_le _, fun a ha => not_writes ?_⟩) fun _ _ _ _ _ _ _ => trivial
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨_, _, rfl, rfl, by simpa using Box.prot_user hB (off := 320) (by decide) a ha⟩
  · exact hn (Prim.dup_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hz (by decide) (fun _ _ _ _ => trivial) fun _ _ _ _ _ _ => trivial
  · exact hn (uvar_frame rfl _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.fetch_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (open_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.zequal_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hz (by decide) (fun _ _ _ _ => trivial) fun _ _ _ _ _ _ => trivial
  · exact hn (twodrop_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hl (fun _ => by decide) fun s _ => ⟨s.ds, rfl⟩
  -- 10: -269 throw, which never returns
  · exact hn (throwM_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨t, ht⟩ := hr
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht
      subst ht
      simp [forth] at h
  · exact hn (uvar_frame rfl _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.fetch_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (tx_room_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (qdup_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.zequal_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hz (by decide) (fun _ _ _ _ => trivial) fun _ _ _ _ _ _ => trivial
  · exact hn (uvar_frame rfl _) (by decide) fun s s' hn _ h _ => by
      rw [uvar_ok rfl s s' h]
      exact ⟨s.ds, by simp only [hn.1]⟩
  · exact hn (Prim.fetch_frame _) (by decide) fun s s' hn hr h _ => by
      obtain ⟨t, ht⟩ := hr
      have hc := onConn_of hp0 hn
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      exact ⟨t, by simp only [hc]⟩
  -- 19: TCP output, for the connection
  · refine hft Words.«tcp-output».foot hN.quiet (by decide) (fun s _ hr => ?_) fun _ _ _ _ _ _ _ => trivial
    obtain ⟨t, ht⟩ := hr
    exact ⟨by simp [ht], fun a ha => by rw [ht]; exact hN.out a ha⟩
  · exact hl (fun _ => by decide) fun s _ => ⟨s.ds, rfl⟩
  -- 21: CATCH of `io-wait`: it returns 0 having kept the setting, or a code
  · intro s pc' s' ⟨hm, hr⟩ hs
    cases hs with
    | call h =>
      refine ⟨fun h' => absurd (by decide) h', ?_⟩
      obtain ⟨hu, hm0⟩ := hm (by decide)
      obtain ⟨t, ht⟩ := hr
      have hc := onConn_of hp0 ⟨hu, hm0⟩
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht hu hc hm0
      subst ht hu
      simp only [catchM] at h
      rw [show dispatch (wordAddr "io-wait") = Words.«io-wait» from Runs.runs] at h
      cases hio : Words.«io-wait» ⟨t, rs, m, B.p, e⟩ with
      | ok st =>
        rw [hio] at h
        cases h
        obtain ⟨hu', hm'⟩ := io_wait_guards hB hN ⟨t, rs, m, B.p, e⟩ st rfl hc hio
        exact Or.inl ⟨st.ds, rfl, hu', fun a ha => (hm' a ha).trans (hm0 a ha)⟩
      | error f =>
        rw [hio] at h
        cases hcode : f.err.code with
        | none => simp [hcode] at h
        | some n =>
          simp only [hcode, Except.ok.injEq] at h
          subst h
          exact Or.inr ⟨n, _, rfl, Err.code_ne_zero hcode⟩
  -- 22: ?dup of the code
  · refine hcd (by decide) fun s s' hr h => ?_
    obtain ⟨hu', hm'⟩ := qdup_frame noCell s s' h
    obtain ⟨x, t, hds, hds'⟩ := qdup_shape s s' h
    rcases hr with ⟨t0, ht0, hnm⟩ | ⟨y, t0, ht0, hy⟩
    · rw [ht0, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      simp only [if_true] at hds'
      exact Or.inl ⟨t0, hds', hu'.trans hnm.1, fun a ha => (hm' a id).trans (hnm.2 a ha)⟩
    · rw [ht0, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      simp only [hy, if_false] at hds'
      exact Or.inr ⟨y, t0, hds', hy⟩
  -- 23: 0 goes on, having kept the setting; a code goes to the reset
  · intro s pc' s' ⟨_, hr⟩ hs
    cases hs with
    | zjump hds =>
      rcases hr with ⟨t, ht, hnm⟩ | ⟨x, t, ht, hx⟩
      · exact ⟨fun _ => hnm, trivial⟩
      · rw [ht, List.cons.injEq] at hds
        exact absurd hds.1 hx
    | zfall hds hx =>
      refine ⟨fun h' => absurd (by decide) h', ?_⟩
      rcases hr with ⟨t, ht, _⟩ | ⟨y, t, ht, hy⟩
      · rw [ht, List.cons.injEq] at hds
        exact absurd hds.1.symm hx
      · rw [ht, List.cons.injEq] at hds
        exact ⟨y, t, hds.2.symm, hy⟩
  · refine hcd (by decide) fun s s' hr h => ?_
    obtain ⟨x, t, ht, hx⟩ := hr
    rw [uvar_ok rfl s s' h]
    exact ⟨s.up + 328, x, t, by simp only [ht], hx⟩
  · refine hcd (by decide) fun s s' hr h => ?_
    obtain ⟨y, x, t, ht, hx⟩ := hr
    obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
    rw [ht, List.cons.injEq] at hds
    obtain ⟨rfl, rfl⟩ := hds
    exact ⟨_, x, t, rfl, hx⟩
  -- 26: reset the connection; the code stays
  · refine hcd (by decide) fun s s' hr h => ?_
    obtain ⟨y, x, t, ht, hx⟩ := hr
    have hd := (foot_drop Words.«abort-connection».foot (by simp [ht]) h).1
    rw [ht] at hd
    simp only [List.drop_zero, List.drop_succ_cons] at hd
    exact ⟨x, t, hd, hx⟩
  -- 27: and throw it
  · intro s pc' s' ⟨_, hr⟩ hs
    cases hs with
    | call h =>
      obtain ⟨x, t, ht, hx⟩ := hr
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht
      subst ht
      simp only [throwM] at h
      split at h
      · rename_i hx0; exact absurd hx0 hx
      · cases h
  · exact hb (fun _ => by decide) fun _ _ => trivial
  -- 29: io-start
  · refine hft Words.«io-start».foot hN.quiet (by decide)
      (fun s _ _ => ⟨Nat.zero_le _, fun a ha => not_writes ?_⟩) fun _ _ _ _ _ _ _ => trivial
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨_, _, rfl, rfl, by simpa using Box.prot_user hB (off := 320) (by decide) a ha⟩
  · exact hn (Prim.over_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (min_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.dup_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hl (fun _ => by decide) fun _ _ => trivial
  · exact hq (by decide) (fun _ => trivial) fun _ => trivial
  · exact hl (fun _ => by decide) fun _ _ => trivial
  · exact hn (pick_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (i_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hn (Prim.plus_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  -- 39: the byte; then its place in the ring
  · exact hn (Prim.cfetch_frame _) (by decide) fun s s' _ _ h _ => by
      obtain ⟨a, t, _, rfl⟩ := cfetch_ok h
      exact ⟨_, t, rfl⟩
  · exact hn (uvar_frame rfl _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨w, t, ht⟩ := hr
      rw [uvar_ok rfl s s' h]
      exact ⟨s.up + 328, w, t, by simp only [ht]⟩
  · exact hn (Prim.fetch_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨x, w, t, ht⟩ := hr
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      exact ⟨_, w, t, rfl⟩
  · exact hn (ctxq_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨x, w, t, ht⟩ := hr
      obtain ⟨y, t', hy, rfl⟩ := field_ok rfl s s' h
      rw [ht, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨_, w, t, rfl⟩
  · exact hn (Prim.fetch_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨x, w, t, ht⟩ := hr
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      exact ⟨_, w, t, rfl⟩
  · exact hn (i_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨x, w, t, ht⟩ := hr
      obtain ⟨v, rfl⟩ := i_ok h
      exact ⟨v, x, w, t, by simp only [ht]⟩
  · exact hn (Prim.plus_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨i, x, w, t, ht⟩ := hr
      obtain ⟨b, a, t', hds, rfl⟩ := bin_ok h
      rw [ht] at hds
      simp only [List.cons.injEq] at hds
      obtain ⟨rfl, rfl, rfl⟩ := hds
      exact ⟨_, w, t, rfl⟩
  · exact hn (slash_tx_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨z, w, t, ht⟩ := hr
      rw [pushConst_ok (v := 8192) h]
      exact ⟨z, w, t, by simp only [ht]⟩
  · exact hn (oneminus_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨z, w, t, ht⟩ := hr
      obtain ⟨x, t', hx, rfl⟩ := oneminus_ok h
      rw [ht, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨z, w, t, rfl⟩
  -- 48: the mask keeps the offset inside the ring
  · exact hn (Prim.and_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨z, w, t, ht⟩ := hr
      obtain ⟨b, a, t', hds, rfl⟩ := bin_ok h
      rw [ht] at hds
      simp only [List.cons.injEq] at hds
      obtain ⟨rfl, rfl, rfl⟩ := hds
      refine ⟨_, w, t, rfl, ?_⟩
      rw [BitVec.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · exact hn (uvar_frame rfl _) (by decide) fun s s' hn hr h _ => by
      obtain ⟨y, w, t, ht, hy⟩ := hr
      rw [uvar_ok rfl s s' h]
      exact ⟨y, w, t, by simp only [ht, hn.1], hy⟩
  · exact hn (Prim.fetch_frame _) (by decide) fun s s' hn hr h _ => by
      obtain ⟨y, w, t, ht, hy⟩ := hr
      have hc := onConn_of hp0 hn
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      exact ⟨y, w, t, by simp only [hc], hy⟩
  · exact hn (ctx_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨y, w, t, ht, hy⟩ := hr
      obtain ⟨x, t', hx, rfl⟩ := field_ok rfl s s' h
      rw [ht, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨y, w, t, rfl, hy⟩
  · exact hn (Prim.plus_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨y, w, t, ht, hy⟩ := hr
      obtain ⟨b, a, t', hds, rfl⟩ := bin_ok h
      rw [ht] at hds
      simp only [List.cons.injEq] at hds
      obtain ⟨rfl, rfl, rfl⟩ := hds
      exact ⟨_, w, t, rfl, hy⟩
  -- 53: the byte into the transmit ring, inside the connection's record
  · refine hft Prim.cstore_foot hN.quiet (by decide) (fun s _ hr => ?_) fun _ _ _ _ _ _ _ => trivial
    obtain ⟨y, w, t, ht, hy⟩ := hr
    refine ⟨by simp [ht], fun a ha => not_writes ?_⟩
    simp only [ht, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    have := hN.apart a ha
    exact ⟨_, _, rfl, rfl, by simp; bv_omega⟩
  · exact hlp (by decide) (fun _ => trivial) fun _ => trivial
  · exact hn (Prim.dup_frame _) (by decide) fun s s' _ _ h _ => by
      obtain ⟨x, t, _, rfl⟩ := dup_ok h
      exact ⟨x, x :: t, rfl⟩
  · exact hn (uvar_frame rfl _) (by decide) fun s s' hn hr h _ => by
      obtain ⟨x, t, ht⟩ := hr
      rw [uvar_ok rfl s s' h]
      exact ⟨x, t, by simp only [ht, hn.1]⟩
  · exact hn (Prim.fetch_frame _) (by decide) fun s s' hn hr h _ => by
      obtain ⟨x, t, ht⟩ := hr
      have hc := onConn_of hp0 hn
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      exact ⟨x, t, by simp only [hc]⟩
  · exact hn (ctxq_frame _) (by decide) fun s s' _ hr h _ => by
      obtain ⟨x, t, ht⟩ := hr
      obtain ⟨y, t', hy, rfl⟩ := field_ok rfl s s' h
      rw [ht, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨x, t, rfl⟩
  -- 59: the count into the connection's `tx-queued`
  · refine hft Words.«+!».foot hN.quiet (by decide) (fun s _ hr => ?_) fun _ _ _ _ _ _ _ => trivial
    obtain ⟨x, t, ht⟩ := hr
    refine ⟨by simp [ht], fun a ha => not_writes ?_⟩
    simp only [ht, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    have := hN.apart a ha
    exact ⟨_, _, rfl, rfl, by simp; bv_omega⟩
  · exact hn (slash_string_frame _) (by decide) fun _ _ _ _ _ _ => trivial
  · exact hb (fun _ => by decide) fun _ _ => trivial
  · exact hn (twodrop_frame _) (by decide) fun _ _ _ _ _ _ => trivial

end

/-! ## `telnet-type` -/

section
variable {B : Box}

/-- What `telnet-type` needs of its stack: the connection it puts in
`cur-conn`, and the connection again for TCP output. -/
def telAt (B : Box) : Nat → List Cell → Prop
  | 1, ds => ∃ t, ds = (B.p + 336) :: t
  | 2, ds => ∃ t, ds = B.conn :: t
  | 3, ds => ∃ t, ds = (B.p + 328) :: B.conn :: t
  | 37, ds => ∃ t, ds = (B.p + 328) :: t
  | 38, ds => ∃ t, ds = B.conn :: t
  | _, _ => True

/-- From the store at 3 on, `cur-conn` holds the session's connection. -/
abbrev telR (B : Box) (pc : Nat) (s : S) : Prop :=
  (4 ≤ pc ∧ pc ≤ 37 → OnConn B s) ∧ telAt B pc s.ds

theorem tk {s0 : S} {pc : Nat} {f : Sem} (hf : Frame noCell f) (h4 : 4 ≤ pc)
    (hR : ∀ s s', telAt B pc s.ds → f s = .ok s' → telAt B (pc + 1) s'.ds) :
    Keeps (GQ B B.supp s0 [] (telR B)) pc (.call f) :=
  hn hf List.not_mem_nil fun s s' _ hr h hm =>
    ⟨fun hp => by unfold OnConn; rw [hm]; exact hr.1 ⟨h4, by omega⟩, hR s s' hr.2 h⟩

theorem tl {s0 : S} {pc : Nat} {v : Cell} (h4 : 4 ≤ pc) (hR : ∀ ds, telAt B (pc + 1) ds) :
    Keeps (GQ B B.supp s0 [] (telR B)) pc (.lit v) :=
  hl (fun _ => List.not_mem_nil) fun _ hr => ⟨fun hp => hr.1 ⟨h4, by omega⟩, hR _⟩

theorem tb {s0 : S} {pc t : Nat} (h4 : 4 ≤ pc) (h37 : pc ≤ 37) (ht : ∀ ds, telAt B t ds) :
    Keeps (GQ B B.supp s0 [] (telR B)) pc (.branch t) :=
  hb (fun _ => List.not_mem_nil) fun _ hr => ⟨fun _ => hr.1 ⟨h4, h37⟩, ht _⟩

theorem tz {s0 : S} {pc t : Nat} (h4 : 4 ≤ pc) (h37 : pc ≤ 37) (ht : ∀ ds, telAt B t ds)
    (hf : ∀ ds, telAt B (pc + 1) ds) : Keeps (GQ B B.supp s0 [] (telR B)) pc (.zbranch t) :=
  hz List.not_mem_nil (fun _ _ _ hr => ⟨fun _ => hr.1 ⟨h4, h37⟩, ht _⟩)
    fun _ _ _ _ _ hr => ⟨fun _ => hr.1 ⟨h4, h37⟩, hf _⟩

/-- `telnet-type` keeps the setting: it points `cur-conn` at the session's
connection, then sends through it. -/
theorem telnet_type_keeps (hB : B.Ok) (hN : B.Net) [Runs "(arp-request)" Words.«(arp-request)»]
    [Runs "(segment-out)" Words.«(segment-out)»] [Runs "(tcp-output)" Words.«(tcp-output)»]
    [Runs "(free-conn)" Words.«(free-conn)»] [Runs "io-wait" Words.«io-wait»] :
    B.Keeps Words.«telnet-type» := by
  have hq : ∀ a, B.supp a → Quiet a := fun a ha => hN.quiet a (Or.inl ha)
  have hsend := send_guards hB hN
  have hconn : ∀ {s s' : S}, OnConn B s → (∀ a, B.prot a → s'.mem a = s.mem a) → OnConn B s' :=
    fun {s s'} hc hm => by
      unfold OnConn at hc ⊢
      rw [rd_congr s'.mem s.mem 8 _ fun i hi => hm _ (Or.inr (by bv_omega))]
      exact hc
  have hgd := (guards_of (B := B) (code := Words.«telnet-type».code) (P := B.supp) (D := []) (R := fun _ => telR B) (pre := fun s => B.Inv s.mem)
    (fun _ _ => List.not_mem_nil) (fun _ _ => ⟨fun h => absurd h.1 (by decide), trivial⟩)
    fun s0 _ hI0 => ?_).2
  · intro s s' hu hI h
    obtain ⟨hu', hm⟩ := hgd s s' hu hI h
    exact ⟨hu', fun a ha => (hm a ha).trans (hI a ha)⟩
  have send_step : ∀ {pc : Nat}, 4 ≤ pc → pc + 1 ≤ 37 → (∀ ds, telAt B (pc + 1) ds) →
      Keeps (GQ B B.supp s0 [] (telR B)) pc (.call Words.«(send)») := fun h4 h37 ht =>
    hg hsend (fun a ha => Or.inl ha) List.not_mem_nil (fun _ _ hr => hr.1 ⟨h4, by omega⟩)
      fun _ _ _ hr _ hm => ⟨fun _ => hconn (hr.1 ⟨h4, by omega⟩) hm, ht _⟩
  simp only [Words.«telnet-type».code, forall_getElem?_cons, forall_getElem?_nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he⟩
  -- 0-3: `term-conn @ cur-conn !`
  · exact hn (uvar_frame rfl _) List.not_mem_nil fun s s' hn _ h _ => by
      rw [uvar_ok rfl s s' h]
      exact ⟨fun hp => absurd hp.1 (by decide), s.ds, by simp only [hn.1]⟩
  · exact hn (Prim.fetch_frame _) List.not_mem_nil fun s s' hn hr h _ => by
      obtain ⟨t, ht⟩ := hr.2
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      refine ⟨fun hp => absurd hp.1 (by decide), t, ?_⟩
      have : rd s.mem (B.p + 336) 8 = B.conn := by
        unfold Box.conn
        exact rd_congr s.mem B.m0 8 _ fun i hi =>
          (hn.2 _ (Or.inl (Or.inr (by bv_omega)))).trans (hI0 _ (Or.inl (Or.inr (by bv_omega))))
      simp only [this]
  · exact hn (uvar_frame rfl _) List.not_mem_nil fun s s' hn hr h _ => by
      obtain ⟨t, ht⟩ := hr.2
      rw [uvar_ok rfl s s' h]
      exact ⟨fun hp => absurd hp.1 (by decide), t, by simp only [ht, hn.1]⟩
  · refine hft Prim.store_foot hq List.not_mem_nil (fun s _ hr => ?_) fun s s' _ hr h _ _ => ?_
    · obtain ⟨t, ht⟩ := hr.2
      refine ⟨by simp [ht], fun a ha => not_writes ?_⟩
      simp only [ht, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨_, _, rfl, rfl, by simpa using Box.supp_apart hB (off := 328) (by decide) a ha⟩
    · obtain ⟨t, ht⟩ := hr.2
      rcases s with ⟨ds, rs, m, u, e⟩
      simp only at ht
      subst ht
      simp only [forth] at h
      cases h
      exact ⟨fun _ => rd_wr_same _ _ _, trivial⟩
  -- 4-36: the loop, and the test for output in flight
  · exact tk (Prim.dup_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tz (by decide) (by decide) (fun _ => trivial) fun _ => trivial
  · exact tk (twodup_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (plain_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (qdup_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tz (by decide) (by decide) (fun _ => trivial) fun _ => trivial
  · exact tk (Prim.tor_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (Prim.over_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (Prim.rfetch_frame _) (by decide) fun _ _ _ _ => trivial
  · exact send_step (by decide) (by decide) fun _ => trivial
  · exact tk (Prim.rfrom_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (slash_string_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tb (by decide) (by decide) fun _ => trivial
  · exact tk (Prim.over_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (Prim.cfetch_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tl (by decide) fun _ => trivial
  · exact tk (Prim.equal_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tz (by decide) (by decide) (fun _ => trivial) fun _ => trivial
  · exact tk (pushConst_frame _ _) (by decide) fun _ _ _ _ => trivial
  · exact tb (by decide) (by decide) fun _ => trivial
  · exact tk (pushConst_frame _ _) (by decide) fun _ _ _ _ => trivial
  · exact tl (by decide) fun _ => trivial
  · exact send_step (by decide) (by decide) fun _ => trivial
  · exact tl (by decide) fun _ => trivial
  · exact tk (slash_string_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tb (by decide) (by decide) fun _ => trivial
  · exact tk (twodrop_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (uvar_frame rfl _) (by decide) fun _ _ _ _ => trivial
  · exact tk (Prim.fetch_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (in_flight_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tk (Prim.zequal_frame _) (by decide) fun _ _ _ _ => trivial
  · exact tz (by decide) (by decide) (fun _ => trivial) fun _ => trivial
  · exact hn (uvar_frame rfl _) List.not_mem_nil fun s s' hn hr h hm => by
      refine ⟨fun _ => ?_, ?_⟩
      · unfold OnConn; rw [hm]; exact hr.1 ⟨by decide, by decide⟩
      · rw [uvar_ok rfl s s' h]; exact ⟨s.ds, by simp only [hn.1]⟩
  -- 37-38: TCP output, for the connection `cur-conn` holds
  · exact hn (Prim.fetch_frame _) List.not_mem_nil fun s s' hn hr h _ => by
      have hc : rd s.mem (B.p + 328) 8 = B.conn := hr.1 ⟨by decide, by decide⟩
      obtain ⟨t, ht⟩ := hr.2
      obtain ⟨a, t', hds, rfl⟩ := fetch_ok h
      rw [ht, List.cons.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      exact ⟨fun hp => absurd hp.2 (by decide), t, by simp only [hc]⟩
  · refine hft Words.«tcp-output».foot hq List.not_mem_nil (fun s _ hr => ?_) fun _ _ _ _ _ _ _ =>
      ⟨fun hp => absurd hp.2 (by decide), trivial⟩
    obtain ⟨t, ht⟩ := hr.2
    exact ⟨by simp [ht], fun a ha => by rw [ht]; exact hN.out a (Or.inl ha)⟩

end

/-! ## Bounded writes

The setting includes every byte outside the task's own memory that nothing
else writes (`Box.dictSupp`), so keeping it is the brief's bounded writes. -/

section
variable {B : Box}

/-- TYPE keeps the setting, on the console or a session. -/
theorem type_keeps_net (hB : B.Ok) (hT : B.Term)
    (hN : dispatch (rd B.m0 (B.p + 144) 8) = Words.«telnet-type» → B.Net)
    [Runs "(arp-request)" Words.«(arp-request)»] [Runs "(segment-out)" Words.«(segment-out)»]
    [Runs "(tcp-output)" Words.«(tcp-output)»] [Runs "(free-conn)" Words.«(free-conn)»]
    [Runs "io-wait" Words.«io-wait»] : B.Keeps Words.«type» := by
  intro s s' hu hI h
  have hd := type_ok s s' h
  rw [hu, B.rd_eq hI _ 8 fun i hi => Or.inl (Or.inr (by bv_omega))] at hd
  rcases hT.type with h1 | h1 <;> rw [h1] at hd
  · exact nk (console_type_frame _) s s' hu hI hd
  · exact telnet_type_keeps hB (hN h1) s s' hu hI hd

/-- Every word in the sandbox keeps the setting. -/
theorem all_keep (hB : B.Ok) (hT : B.Term)
    (hN : dispatch (rd B.m0 (B.p + 144) 8) = Words.«telnet-type» → B.Net)
    [Runs "(arp-request)" Words.«(arp-request)»] [Runs "(segment-out)" Words.«(segment-out)»]
    [Runs "(tcp-output)" Words.«(tcp-output)»] [Runs "(free-conn)" Words.«(free-conn)»]
    [Runs "io-wait" Words.«io-wait»] : ∀ f ∈ Words.«sandbox-wordlist».words, B.Keeps f :=
  sandbox_keeps hB (output_keeps hB (type_keeps_net hB hT hN) (bye_keeps hB hT))

/-- **Bounded writes, word by word.** Each exposed word, run in the sandboxed
task, leaves every byte outside the task's own memory that nothing else
writes as it was. -/
theorem bounded_writes (hB : B.Ok) (hT : B.Term)
    (hN : dispatch (rd B.m0 (B.p + 144) 8) = Words.«telnet-type» → B.Net)
    [Runs "(arp-request)" Words.«(arp-request)»] [Runs "(segment-out)" Words.«(segment-out)»]
    [Runs "(tcp-output)" Words.«(tcp-output)»] [Runs "(free-conn)" Words.«(free-conn)»]
    [Runs "io-wait" Words.«io-wait»] :
    ∀ f ∈ Words.«sandbox-wordlist».words, ∀ s s', s.up = B.p → B.Inv s.mem → f s = .ok s' →
      ∀ a, ¬ B.own a → Quiet a → s'.mem a = s.mem a := by
  intro f hf s s' hu hI h a ha hq
  have hs : B.supp a := Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hq⟩)))
  rw [(all_keep hB hT hN f hf s s' hu hI h).2 a hs, hI a hs]

/-- **Bounded writes, for a line.** A sandboxed INTERPRET that finishes leaves
every byte outside the task's own memory that nothing else writes as it was
when the line began. -/
theorem line_bounded (hB : B.Ok) (hT : B.Term)
    (hN : dispatch (rd B.m0 (B.p + 144) 8) = Words.«telnet-type» → B.Net)
    [Runs "(arp-request)" Words.«(arp-request)»] [Runs "(segment-out)" Words.«(segment-out)»]
    [Runs "(tcp-output)" Words.«(tcp-output)»] [Runs "(free-conn)" Words.«(free-conn)»]
    [Runs "io-wait" Words.«io-wait»]
    (hdump : ∀ h ∈ B.hs, ∃ f ∈ Words.«sandbox-wordlist».words, dispatch (Box.xtOf B.m0 h) = f)
    (s s' : S) (hu : s.up = B.p) (hm : s.mem = B.m0) (h : Words.«interpret» s = .ok s') :
    ∀ a, ¬ B.own a → Quiet a → s'.mem a = B.m0 a := by
  have hkeep : ∀ xt s s', B.Allowed xt → s.up = B.p → B.Inv s.mem → dispatch xt s = .ok s' →
      s'.up = B.p ∧ B.Inv s'.mem := by
    rintro xt s s' ⟨hh, hhs, rfl⟩ hu hI hx
    obtain ⟨f, hf, heq⟩ := hdump hh hhs
    rw [heq] at hx
    exact all_keep hB hT hN f hf s s' hu hI hx
  have go : ∀ n, run Words.«interpret».code n 0 s = .ok s' → B.Inv s'.mem := by
    intro n hr
    obtain ⟨pe, hpe, hq, _⟩ := run_inv _ _ (interpret_inv hB hkeep) n 0 s s'
      ⟨fun _ => ⟨hu, fun a _ => by rw [hm]⟩, trivial⟩ hr
    have h17 : pe ≠ 17 ∧ pe ≠ 18 := by
      constructor <;> rintro rfl <;> simp [Words.«interpret».code] at hpe
    exact (hq h17).2
  intro a ha hq
  have hs : B.supp a := Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hq⟩)))
  show s'.mem a = B.m0 a
  unfold Words.«interpret» loopThread at h
  split at h
  · exact go _ h a hs
  · simp [S.fail] at h

end

/-- **Sandbox isolation.** A task whose search order is the sandbox alone, on
the console or a network session, executes only the sandbox's words, for any
line. Assumed: the dump's headers (`hdump`); for a session, what its terminal
rests on (`Box.Net`); and that the words the network runs by xt are the ones
named (`Runs`). -/
theorem isolated (B : Box) (hB : B.Ok) (hT : B.Term)
    (hN : dispatch (rd B.m0 (B.p + 144) 8) = Words.«telnet-type» → B.Net)
    [Runs "(arp-request)" Words.«(arp-request)»] [Runs "(segment-out)" Words.«(segment-out)»]
    [Runs "(tcp-output)" Words.«(tcp-output)»] [Runs "(free-conn)" Words.«(free-conn)»]
    [Runs "io-wait" Words.«io-wait»]
    (hdump : ∀ h ∈ B.hs, ∃ f ∈ Words.«sandbox-wordlist».words, dispatch (Box.xtOf B.m0 h) = f)
    (d : Cell → Sem) (hd : ∀ xt, B.Allowed xt → d xt = dispatch xt)
    (s : S) (hu : s.up = B.p) (hm : s.mem = B.m0) :
    loopThread (Words.«interpret».code.set 29 (.call (execWith d))) s = Words.«interpret» s := by
  exact isolated_given_terminal B hB hdump (type_keeps_net hB hT hN) (bye_keeps hB hT) d hd s hu hm

end OS4.Isolation

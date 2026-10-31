import OS4.Footprint
import OS4.Memory
import OS4.PrimSpecs

/-!
# The primitives' footprints

Each primitive's Foot, proven from its model: the stores write their cell,
`fill` and `cmove` their range, a system call or SHA-256 anywhere, and the
rest nothing. Stack primitives say where their outputs came from, which lets
callers follow an address through `swap`, `>r` and the like.
-/

namespace OS4

/-- Run a primitive that writes nothing on its cases, and check its outputs. -/
macro "prim_foot" : tactic => `(tactic| (
  intro xs zs s r m u e hx hz
  rcases xs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, xs⟩⟩⟩⟩⟩⟩ <;>
  rcases zs with _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨z4, zs⟩⟩⟩⟩ <;>
  simp_all [forth, FOut, Kept, resMem, agree_cons, agree_nil, Val.holds, Val.eval] <;>
  (repeat' split) <;>
  (try simp_all [FOut, Kept, resMem, agree_cons, agree_nil, Val.holds, Val.eval]) <;> omega))

theorem kept_all {ρ : Env} {m0 m : Mem} : Kept [Reg.all] ρ m0 m := by
  intro a _ hw
  exact absurd ⟨Reg.all, List.mem_singleton_self _, fun b l hb _ => by simp [Reg.all, Val.eval] at hb⟩ hw

/-- Outside a single region whose base and length are known. -/
theorem outside_one {base len : Val} {ρ : Env} {a b l : Cell} (hb : base.eval ρ = some b)
    (hl : len.eval ρ = some l) (hw : ¬ Writes [⟨base, len⟩] ρ a) :
    ∀ j, j < l.toNat → a ≠ b + BitVec.ofNat 64 j := by
  intro j hj heq
  apply hw
  refine ⟨_, List.mem_singleton_self _, fun b' l' hb' hl' => ?_⟩
  simp only [hb, Option.some.injEq] at hb'
  simp only [hl, Option.some.injEq] at hl'
  subst hb' hl' heq
  have : b + BitVec.ofNat 64 j - b = BitVec.ofNat 64 j := by bv_omega
  rw [this, BitVec.toNat_ofNat]
  omega

theorem fillM_other (x : Cell) : ∀ (n : Nat) (m : Mem) (a : Cell) (c : BitVec 8),
    (∀ j, j < n → x ≠ a + BitVec.ofNat 64 j) → Prim.fillM n m a c x = m x := by
  intro n
  induction n with
  | zero => intro m a c _; rfl
  | succ n ih =>
    intro m a c h
    simp only [Prim.fillM]
    rw [ih]
    · have := h 0 (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      simp [upd, this]
    · intro j hj
      rw [← add_ofNat_succ]
      exact h (j + 1) (by omega)

theorem cmoveM_other (x : Cell) : ∀ (n : Nat) (m : Mem) (src dst : Cell),
    (∀ j, j < n → x ≠ dst + BitVec.ofNat 64 j) → Prim.cmoveM n m src dst x = m x := by
  intro n
  induction n with
  | zero => intro m src dst _; rfl
  | succ n ih =>
    intro m src dst h
    simp only [Prim.cmoveM]
    rw [ih]
    · have := h 0 (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      simp [upd, this]
    · intro j hj
      rw [← add_ofNat_succ]
      exact h (j + 1) (by omega)

theorem cmoveUpM_other (x : Cell) : ∀ (n : Nat) (m : Mem) (src dst : Cell),
    (∀ j, j < n → x ≠ dst + BitVec.ofNat 64 j) → Prim.cmoveUpM n m src dst x = m x := by
  intro n
  induction n with
  | zero => intro m src dst _; rfl
  | succ n ih =>
    intro m src dst h
    simp only [Prim.cmoveUpM]
    rw [ih _ _ _ (fun j hj => h j (by omega))]
    simp [upd, h n (by omega)]

/-- A store of n bytes, as a Foot. -/
theorem store_foot {f : Sem} {n : Nat} (hn : n ≤ 8)
    (hf : ∀ a x s r m u e, f ⟨a :: x :: s, r, m, u, e⟩ = .ok ⟨s, r, wr m a n x, u, e⟩) :
    Foot f 2 0 0 0 [⟨.arg 0 0, .num (BitVec.ofNat 64 n)⟩] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [a, x], [], _, _ =>
    simp only [List.cons_append, List.nil_append, hf]
    refine ⟨fun b _ hw => ?_, by simp [FOut, agree_nil]⟩
    apply wr_apply_other
    have h := outside_one (ρ := ⟨[a, x], [], u⟩) (a := b) (b := a) (l := BitVec.ofNat 64 n)
      (by simp [Val.eval]) (by simp [Val.eval]) hw
    intro j hj
    exact h j (by rw [BitVec.toNat_ofNat]; omega)

namespace Prim

theorem dup_foot : Foot dup 1 2 0 0 [] [.arg 0 0, .arg 0 0] [] := by prim_foot
theorem drop_foot : Foot drop 1 0 0 0 [] [] [] := by prim_foot
theorem swap_foot : Foot swap 2 2 0 0 [] [.arg 1 0, .arg 0 0] [] := by prim_foot
theorem over_foot : Foot over 2 3 0 0 [] [.arg 1 0, .arg 0 0, .arg 1 0] [] := by prim_foot
theorem tor_foot : Foot tor 1 0 0 1 [] [] [.arg 0 0] := by prim_foot
theorem rfrom_foot : Foot rfrom 0 1 1 0 [] [.rarg 0 0] [] := by prim_foot
theorem rfetch_foot : Foot rfetch 0 1 1 1 [] [.rarg 0 0] [.rarg 0 0] := by prim_foot
theorem pick_foot : Foot pick 1 1 0 0 [] [.any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [x], [], _, _ =>
    simp only [List.cons_append, List.nil_append, pick]
    split <;> simp [FOut, Kept, resMem, agree_cons, agree_nil, holds_any] <;> omega
theorem depth_foot : Foot depth 0 1 0 0 [] [.any] [] := by prim_foot
theorem bin_foot (f : Cell → Cell → Cell) : Foot (bin f) 2 1 0 0 [] [.any] [] := by prim_foot
theorem un_foot (f : Cell → Cell) : Foot (un f) 1 1 0 0 [] [.any] [] := by prim_foot
theorem plus_foot : Foot plus 2 1 0 0 [] [.sum (.arg 1 0) (.arg 0 0)] [] := by prim_foot
theorem minus_foot : Foot minus 2 1 0 0 [] [.any] [] := bin_foot _
theorem star_foot : Foot star 2 1 0 0 [] [.any] [] := bin_foot _
theorem and_foot : Foot and 2 1 0 0 [] [.any] [] := bin_foot _
theorem or_foot : Foot or 2 1 0 0 [] [.any] [] := bin_foot _
theorem xor_foot : Foot xor 2 1 0 0 [] [.any] [] := bin_foot _
theorem invert_foot : Foot invert 1 1 0 0 [] [.any] [] := un_foot _
theorem lshift_foot : Foot lshift 2 1 0 0 [] [.any] [] := bin_foot _
theorem rshift_foot : Foot rshift 2 1 0 0 [] [.any] [] := bin_foot _
theorem equal_foot : Foot equal 2 1 0 0 [] [.any] [] := bin_foot _
theorem less_foot : Foot less 2 1 0 0 [] [.any] [] := bin_foot _
theorem uless_foot : Foot uless 2 1 0 0 [] [.any] [] := bin_foot _
theorem zequal_foot : Foot zequal 1 1 0 0 [] [.any] [] := un_foot _
theorem zless_foot : Foot zless 1 1 0 0 [] [.any] [] := un_foot _
theorem slashmod_foot : Foot slashmod 2 2 0 0 [] [.any, .any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [d, n], [], _, _ =>
    simp only [List.cons_append, List.nil_append, slashmod]
    split
    · simp [FOut, Kept, resMem]
    · split <;> simp [FOut, Kept, resMem, agree_cons, agree_nil, holds_any] <;> omega
theorem umstar_foot : Foot umstar 2 2 0 0 [] [.any, .any] [] := by prim_foot
theorem umslashmod_foot : Foot umslashmod 3 2 0 0 [] [.any, .any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [d, hi, lo], [], _, _ =>
    simp only [List.cons_append, List.nil_append, umslashmod]
    split
    · simp [FOut, Kept, resMem]
    · split
      · simp [FOut, Kept, resMem]
      · simp [FOut, Kept, resMem, agree_cons, agree_nil, holds_any]; try omega
theorem fetch_foot : Foot fetch 1 1 0 0 [] [.any] [] := by prim_foot
theorem cfetch_foot : Foot cfetch 1 1 0 0 [] [.any] [] := by prim_foot
theorem wfetch_foot : Foot wfetch 1 1 0 0 [] [.any] [] := by prim_foot
theorem lfetch_foot : Foot lfetch 1 1 0 0 [] [.any] [] := by prim_foot
theorem store_foot : Foot store 2 0 0 0 [⟨.arg 0 0, .num 8⟩] [] [] :=
  OS4.store_foot (n := 8) (by omega) (fun _ _ _ _ _ _ _ => rfl)
theorem cstore_foot : Foot cstore 2 0 0 0 [⟨.arg 0 0, .num 1⟩] [] [] :=
  OS4.store_foot (n := 1) (by omega) (fun _ _ _ _ _ _ _ => rfl)
theorem wstore_foot : Foot wstore 2 0 0 0 [⟨.arg 0 0, .num 2⟩] [] [] :=
  OS4.store_foot (n := 2) (by omega) (fun _ _ _ _ _ _ _ => rfl)
theorem lstore_foot : Foot lstore 2 0 0 0 [⟨.arg 0 0, .num 4⟩] [] [] :=
  OS4.store_foot (n := 4) (by omega) (fun _ _ _ _ _ _ _ => rfl)

/-- `cmove` and `cmove>` ( src dst n -- ) write n bytes at dst. -/
theorem cmove_foot : Foot cmove 3 0 0 0 [⟨.arg 1 0, .arg 0 0⟩] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [n, dst, src], [], _, _ =>
    simp only [List.cons_append, List.nil_append, cmove]
    refine ⟨fun b _ hw => ?_, by simp [FOut, agree_nil]⟩
    exact cmoveM_other _ _ _ _ _ (outside_one (ρ := ⟨[n, dst, src], [], u⟩) (b := dst) (l := n)
      (by simp [Val.eval]) (by simp [Val.eval]) hw)
theorem cmoveUp_foot : Foot cmoveUp 3 0 0 0 [⟨.arg 1 0, .arg 0 0⟩] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [n, dst, src], [], _, _ =>
    simp only [List.cons_append, List.nil_append, cmoveUp]
    refine ⟨fun b _ hw => ?_, by simp [FOut, agree_nil]⟩
    exact cmoveUpM_other _ _ _ _ _ (outside_one (ρ := ⟨[n, dst, src], [], u⟩) (b := dst) (l := n)
      (by simp [Val.eval]) (by simp [Val.eval]) hw)
/-- `fill` ( addr n c -- ) writes n bytes at addr. -/
theorem fill_foot : Foot fill 3 0 0 0 [⟨.arg 2 0, .arg 1 0⟩] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [c, n, a], [], _, _ =>
    simp only [List.cons_append, List.nil_append, fill]
    refine ⟨fun b _ hw => ?_, by simp [FOut, agree_nil]⟩
    exact fillM_other _ _ _ _ _ (outside_one (ρ := ⟨[c, n, a], [], u⟩) (b := a) (l := n)
      (by simp [Val.eval]) (by simp [Val.eval]) hw)

theorem upfetch_foot : Foot upfetch 0 1 0 0 [] [.user 0] [] := by prim_foot
theorem pdo_foot : Foot pdo 2 0 0 2 [] [] [.arg 0 0, .arg 1 0] := by prim_foot
theorem i_foot : Foot i 0 1 1 1 [] [.rarg 0 0] [.rarg 0 0] := by prim_foot
theorem j_foot : Foot j 0 1 3 3 [] [.rarg 2 0] [.rarg 0 0, .rarg 1 0, .rarg 2 0] := by prim_foot
theorem unloop_foot : Foot unloop 0 0 2 0 [] [] [] := by prim_foot
/-- PAUSE writes nothing itself: what changes is the outside world's doing. -/
theorem pause_foot : Foot pause 0 0 0 0 [] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ =>
    refine ⟨fun a hq _ => hq _ _, by simp [pause, FOut, agree_nil]⟩
theorem ask_foot : Foot ask 0 1 0 0 [] [.any] [] := by prim_foot
theorem emit_foot : Foot emit 1 0 0 0 [] [] [] := by prim_foot
theorem syscall_foot : Foot syscall 5 1 0 0 [Reg.all] [.any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [_, _, _, _, _], [], _, _ =>
    exact ⟨kept_all, by simp [syscall, FOut, agree_cons, agree_nil, holds_any]; omega⟩
theorem bye_foot : Foot bye 0 0 0 0 [] [] [] := by prim_foot
theorem barrier_foot : Foot barrier 0 0 0 0 [] [] [] := by prim_foot
theorem sha256block_foot : Foot sha256block 4 0 0 0 [Reg.all] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [_, _, _, _], [], _, _ => exact ⟨kept_all, by simp [sha256block, FOut, agree_nil]⟩
theorem sha256out_foot : Foot sha256out 2 0 0 0 [Reg.all] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [_, _], [], _, _ => exact ⟨kept_all, by simp [sha256out, FOut, agree_nil]⟩

/-- `,` writes at the dictionary pointer, an address it reads from memory. -/
theorem comma_foot : Foot comma 1 0 0 0 [Reg.all] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [x], [], _, _ =>
    refine ⟨kept_all, ?_⟩
    simp only [List.cons_append, List.nil_append, comma]
    split <;> simp [FOut, agree_nil]
theorem header_foot : Foot header 2 0 0 0 [Reg.all] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [n, a], [], _, _ =>
    refine ⟨kept_all, ?_⟩
    simp only [List.cons_append, List.nil_append, header]
    repeat' split
    all_goals simp [FOut, agree_nil]
theorem searchList_foot : Foot searchList 3 1 0 0 [] [.any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [nt, n, a], [], _, _ =>
    simp only [List.cons_append, List.nil_append, searchList]
    split <;> simp [FOut, Kept, resMem, agree_cons, agree_nil, holds_any] <;> omega
/-- The parsing words write only `>in`. -/
theorem parseName_foot : Foot parseName 0 2 0 0 [⟨.user 16, .num 8⟩] [.any, .any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ =>
    have keep : ∀ v b, ¬ Writes [⟨.user 16, .num 8⟩] ⟨[], [], u⟩ b → wr m (u + 16) 8 v b = m b := by
      intro v b hw
      apply wr_apply_other
      exact outside_one (ρ := ⟨[], [], u⟩) (b := u + 16) (l := 8) (by simp [Val.eval]) (by simp [Val.eval]) hw
    simp only [List.nil_append, parseName]
    split
    · exact ⟨fun b _ hw => keep _ b hw, by simp [FOut, agree_cons, agree_nil, holds_any]; omega⟩
    · exact ⟨fun b _ hw => keep _ b hw, by simp [FOut, agree_cons, agree_nil, holds_any]; omega⟩
theorem parse_foot : Foot parse 1 2 0 0 [⟨.user 16, .num 8⟩] [.any, .any] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [c], [], _, _ =>
    simp only [List.cons_append, List.nil_append, parse]
    refine ⟨fun b _ hw => ?_, by simp [FOut, agree_cons, agree_nil, holds_any]; omega⟩
    apply wr_apply_other
    exact outside_one (ρ := ⟨[c], [], u⟩) (b := u + 16) (l := 8) (by simp [Val.eval]) (by simp [Val.eval]) hw
theorem paren_foot : Foot paren 0 0 0 0 [⟨.user 16, .num 8⟩] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ =>
    simp only [List.nil_append, paren]
    refine ⟨fun b _ hw => ?_, by simp [FOut, agree_nil]⟩
    apply wr_apply_other
    exact outside_one (ρ := ⟨[], [], u⟩) (b := u + 16) (l := 8) (by simp [Val.eval]) (by simp [Val.eval]) hw

end Prim

theorem throwM_foot : Foot throwM 1 0 0 0 [] [] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [n], [], _, _ =>
    simp only [List.cons_append, List.nil_append, throwM]
    split <;> simp [FOut, Kept, resMem, agree_nil]

theorem pushConst_foot (v : Cell) (lv : Val) (h : ∀ ρ, lv.holds ρ v) :
    Foot (pushConst v) 0 1 0 0 [] [lv] [] := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ => simp [pushConst, FOut, Kept, resMem, agree_cons, agree_nil, h]; omega

theorem kconst_foot (name : String) : Foot (kconst name) 0 1 0 0 [] [.any] [] := by prim_foot

theorem userAt_foot (off : Cell) : Foot (userAt off) 0 1 0 0 [] [.user off] [] := by prim_foot

/-- The return-stack inputs, as a word sees them at entry. -/
def rargList (n : Nat) : List Val := (List.range n).map fun i => .rarg i 0

theorem agree_rargs {ρ : Env} : Agree ρ (rargList ρ.rs.length) ρ.rs := by
  intro i v x h1 h2
  have hi : i < ρ.rs.length := (List.getElem?_eq_some_iff.mp h2).1
  simp [rargList, hi] at h1
  subst h1
  intro c hc
  simp [Val.eval, h2] at hc
  exact hc

/-- A DOES> child: its code's Foot, with the body's address for the code's
first input. -/
theorem doesChild_foot {code : Sem} {k j rk rj : Nat} {regs : List Reg} {dout rout : List Val}
    (b : Cell) (bv : Val) (hb : ∀ ρ, bv.holds ρ b) (h : Foot code (k + 1) j rk rj regs dout rout)
    {regs' : List Reg} {dout' rout' : List Val}
    (hr : regs.map (Reg.subst (bv :: argList k) (rargList rk)) = regs')
    (hd : dout.map (Val.subst (bv :: argList k) (rargList rk)) = dout')
    (hro : rout.map (Val.subst (bv :: argList k) (rargList rk)) = rout') :
    Foot (doesChild b code) k j rk rj regs' dout' rout' := by
  intro xs zs s r m u e hx hz
  subst hr hd hro
  have hc := h (b :: xs) zs s r m u e (by simp [hx]) hz
  let ρ : Env := ⟨xs, zs, u⟩
  have hD : Agree ρ (bv :: argList k) (b :: xs) := by
    rw [agree_cons]
    refine ⟨hb ρ, ?_⟩
    have := agree_args (ρ := ρ)
    simp only [ρ, hx] at this
    exact this
  have hDl : (bv :: argList k).length = (b :: xs).length := by simp [argList, hx]
  have hR : Agree ρ (rargList rk) zs := by
    have := agree_rargs (ρ := ρ)
    simp only [ρ, hz] at this
    exact this
  have hRl : (rargList rk).length = zs.length := by simp [rargList, hz]
  simp only [doesChild, List.cons_append] at hc ⊢
  obtain ⟨hk, ho⟩ := hc
  refine ⟨fun a hq hw => hk a hq fun ⟨r', hr', hh⟩ => hw ⟨_, List.mem_map_of_mem hr',
    has_subst (ρ := ρ) hD hDl hR hRl hh⟩, ?_⟩
  revert ho
  cases code ⟨b :: (xs ++ s), zs ++ r, m, u, e⟩ with
  | error _ => intro _; trivial
  | ok st =>
    rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, agree_subst (ρ := ρ) hD hDl hR hRl h3, h4, h5, agree_subst (ρ := ρ) hD hDl hR hRl h6, h7⟩

end OS4

import OS4.Spec

/-!
# The primitives' stack effects

Each primitive's Spec, proven from its model by cases on the input lists.
-/

namespace OS4

/-- Split the input lists into their items, run the primitive, and count. -/
macro "prim_spec" : tactic => `(tactic| (
  intro xs zs s r m u e hx hz
  rcases xs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, xs⟩⟩⟩⟩⟩⟩ <;>
  rcases zs with _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨z4, zs⟩⟩⟩⟩ <;>
  simp_all [forth, Out, exists_prefix] <;>
  (repeat' split) <;> (try simp_all [Out, exists_prefix]) <;> omega))

namespace Prim

theorem dup_spec : Spec dup 1 2 0 0 := by prim_spec
theorem drop_spec : Spec drop 1 0 0 0 := by prim_spec
theorem swap_spec : Spec swap 2 2 0 0 := by prim_spec
theorem over_spec : Spec over 2 3 0 0 := by prim_spec
theorem tor_spec : Spec tor 1 0 0 1 := by prim_spec
theorem rfrom_spec : Spec rfrom 0 1 1 0 := by prim_spec
theorem rfetch_spec : Spec rfetch 0 1 1 1 := by prim_spec
theorem pick_spec : Spec pick 1 1 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [x], [], _, _ =>
    simp only [List.cons_append, List.nil_append, pick]
    split <;> (simp [Out, exists_prefix]; try omega)
theorem depth_spec : Spec depth 0 1 0 0 := by prim_spec
theorem bin_spec (f : Cell → Cell → Cell) : Spec (bin f) 2 1 0 0 := by prim_spec
theorem un_spec (f : Cell → Cell) : Spec (un f) 1 1 0 0 := by prim_spec
theorem plus_spec : Spec plus 2 1 0 0 := bin_spec _
theorem minus_spec : Spec minus 2 1 0 0 := bin_spec _
theorem star_spec : Spec star 2 1 0 0 := bin_spec _
theorem and_spec : Spec and 2 1 0 0 := bin_spec _
theorem or_spec : Spec or 2 1 0 0 := bin_spec _
theorem xor_spec : Spec xor 2 1 0 0 := bin_spec _
theorem invert_spec : Spec invert 1 1 0 0 := un_spec _
theorem lshift_spec : Spec lshift 2 1 0 0 := bin_spec _
theorem rshift_spec : Spec rshift 2 1 0 0 := bin_spec _
theorem equal_spec : Spec equal 2 1 0 0 := bin_spec _
theorem less_spec : Spec less 2 1 0 0 := bin_spec _
theorem uless_spec : Spec uless 2 1 0 0 := bin_spec _
theorem zequal_spec : Spec zequal 1 1 0 0 := un_spec _
theorem zless_spec : Spec zless 1 1 0 0 := un_spec _
theorem slashmod_spec : Spec slashmod 2 2 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [d, n], [], _, _ =>
    simp only [List.cons_append, List.nil_append, slashmod]
    split
    · simp [Out]
    · split <;> (simp [Out, exists_prefix]; try omega)
theorem umstar_spec : Spec umstar 2 2 0 0 := by prim_spec
theorem umslashmod_spec : Spec umslashmod 3 2 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [d, hi, lo], [], _, _ =>
    simp only [List.cons_append, List.nil_append, umslashmod]
    split
    · simp [Out]
    · split
      · simp [Out]
      · simp [Out, exists_prefix]; try omega
theorem fetch_spec : Spec fetch 1 1 0 0 := by prim_spec
theorem store_spec : Spec store 2 0 0 0 := by prim_spec
theorem cfetch_spec : Spec cfetch 1 1 0 0 := by prim_spec
theorem cstore_spec : Spec cstore 2 0 0 0 := by prim_spec
theorem wfetch_spec : Spec wfetch 1 1 0 0 := by prim_spec
theorem wstore_spec : Spec wstore 2 0 0 0 := by prim_spec
theorem lfetch_spec : Spec lfetch 1 1 0 0 := by prim_spec
theorem lstore_spec : Spec lstore 2 0 0 0 := by prim_spec
theorem cmove_spec : Spec cmove 3 0 0 0 := by prim_spec
theorem cmoveUp_spec : Spec cmoveUp 3 0 0 0 := by prim_spec
theorem fill_spec : Spec fill 3 0 0 0 := by prim_spec
theorem upfetch_spec : Spec upfetch 0 1 0 0 := by prim_spec
theorem pdo_spec : Spec pdo 2 0 0 2 := by prim_spec
theorem i_spec : Spec i 0 1 1 1 := by prim_spec
theorem j_spec : Spec j 0 1 3 3 := by prim_spec
theorem unloop_spec : Spec unloop 0 0 2 0 := by prim_spec
theorem pause_spec : Spec pause 0 0 0 0 := by prim_spec
theorem ask_spec : Spec ask 0 1 0 0 := by prim_spec
theorem emit_spec : Spec emit 1 0 0 0 := by prim_spec
theorem syscall_spec : Spec syscall 5 1 0 0 := by prim_spec
theorem bye_spec : Spec bye 0 0 0 0 := by prim_spec
theorem barrier_spec : Spec barrier 0 0 0 0 := by prim_spec
theorem sha256block_spec : Spec sha256block 4 0 0 0 := by prim_spec
theorem sha256out_spec : Spec sha256out 2 0 0 0 := by prim_spec
theorem comma_spec : Spec comma 1 0 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [x], [], _, _ =>
    simp only [List.cons_append, List.nil_append, comma]
    split <;> simp [Out, exists_prefix] <;> omega
theorem searchList_spec : Spec searchList 3 1 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [nt, n, a], [], _, _ =>
    simp only [List.cons_append, List.nil_append, searchList]
    split <;> simp [Out, exists_prefix] <;> omega
theorem parseName_spec : Spec parseName 0 2 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ =>
    simp only [List.nil_append, parseName]
    split <;> simp [Out, exists_prefix] <;> omega
theorem parse_spec : Spec parse 1 2 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [c], [], _, _ => simp [parse, Out, exists_prefix]; omega
theorem paren_spec : Spec paren 0 0 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [], [], _, _ => simp [paren, Out, exists_prefix]
theorem header_spec : Spec header 2 0 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [n, a], [], _, _ =>
    simp only [List.cons_append, List.nil_append, header]
    repeat' split
    all_goals simp [Out, exists_prefix]

end Prim

theorem userAt_spec (off : Cell) : Spec (userAt off) 0 1 0 0 := by prim_spec

theorem throwM_spec : Spec throwM 1 0 0 0 := by
  intro xs zs s r m u e hx hz
  match xs, zs, hx, hz with
  | [n], [], _, _ =>
    simp only [List.cons_append, List.nil_append, throwM]
    split <;> simp [Out, exists_prefix] <;> omega

end OS4

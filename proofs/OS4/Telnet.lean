import OS4.Terminal
import OS4.Footprint

/-!
# The connection's output (V2)

`isolated_given_telnet` assumed that `telnet-type` keeps the setting. It
sends through the task's connection: it writes the connection's record, the
frames it builds and the network's variables, and it pauses. Here the words it
calls are shown to keep the setting from their footprints, where the world
leaves the support alone and their regions miss it.
-/

namespace OS4.Isolation
open OS4

section
variable {B : Box}

/-- A word with a footprint keeps the setting, where nothing else writes the
support and the word's regions, in terms of the stack it is given, miss it. -/
theorem keeps_of_foot {f : Sem} {k j : Nat} {regs : List Reg} {dout : List Val}
    (hf : Foot f k j 0 0 regs dout []) (hq : ∀ a, B.supp a → Quiet a)
    {s s' : S} (hk : k ≤ s.ds.length) (hw : ∀ a, B.supp a → ¬ Writes regs ⟨s.ds.take k, [], s.up⟩ a)
    (hu : s.up = B.p) (hI : B.Inv s.mem) (h : f s = .ok s') : s'.up = B.p ∧ B.Inv s'.mem := by
  rcases s with ⟨ds, rs, m, u, e⟩
  have hft := hf (ds.take k) [] (ds.drop k) rs m u e
    (by rw [List.length_take]; exact Nat.min_eq_left hk) rfl
  simp only [List.take_append_drop, List.nil_append, h, resMem, FOut] at hft
  obtain ⟨hkept, hfo⟩ := hft
  refine ⟨hfo.2.2.2.2.2.2.trans hu, fun a ha => ?_⟩
  rw [hkept a (hq a ha) (hw a ha)]
  exact hI a ha

end

end OS4.Isolation

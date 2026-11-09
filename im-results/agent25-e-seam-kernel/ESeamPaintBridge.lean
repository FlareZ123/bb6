import ESeamPhysicalBridge
import ESeamPaintCoupling

namespace BB6.PhysicalWindow.ESeam
open BB6.PhysicalWindow

private theorem paint_cell1 (c : Physical) :
    cell (paint c) 1 = cell c 1 := by
  simp [cell, paint, Nat.testBit_or,
    Nat.testBit_one_eq_true_iff_self_eq_zero]

/-- The 6399-node certified E3 safety invariant also governs the E_m (m>=4)
    local prefix, whose only difference inside the protected window is bit0.
    This is a quantified exact all-time physical tape result; original-source
    zipper transport remains a separate obligation. -/
theorem seed0_marker_safe (r : Nat) (remote : Nat → Bool)
    (hr : r < 128) (t : Nat)
    (hm : (run t (seed0 r remote)).pos = 1) :
    (run t (seed0 r remote)).state = 2 ∧
      cell (run t (seed0 r remote)) 1 = true := by
  let c := run t (seed0 r remote)
  have hbridge := paint_run (seed0 r remote)
    (seed0_wf r remote hr) (seed0_marker1 r remote) t
  have hseed := paint_seed0 r remote
  have hfull : run t (seed r remote) = paint c := by
    rw [←hseed, hbridge]
  have hpos : (run t (seed r remote)).pos = 1 := by
    rw [hfull]
    exact hm
  have hs := original_e_base_marker_safe r remote hr t hpos
  rw [hfull] at hs
  change (paint c).state = 2 ∧ cell (paint c) 1 = true at hs
  exact ⟨hs.1, by simpa only [paint_cell1] using hs.2⟩

#print axioms seed0_marker_safe
end BB6.PhysicalWindow.ESeam

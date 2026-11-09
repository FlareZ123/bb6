import ESeamTerminalClassification
import ESeamPaintBridge

namespace BB6.PhysicalWindow.ESeam
open BB6.PhysicalWindow

/-- All first stopped events from the alternate E_m (m>=4) local prefix,
    arbitrary unbounded right tape and arbitrary natural execution time,
    are either C/1 at the protected marker or the real F/1 halt gate. -/
theorem seed0_terminal_classification (r : Nat) (remote : Nat → Bool)
    (hr : r < 128) (t : Nat)
    (ht : terminal (run t (seed0 r remote)) = true) :
    ((run t (seed0 r remote)).pos = 1 ∧
      (run t (seed0 r remote)).state = 2 ∧
      cell (run t (seed0 r remote)) 1 = true) ∨
    ((run t (seed0 r remote)).state = 5 ∧
      scanned (run t (seed0 r remote)) = 1) := by
  let c := run t (seed0 r remote)
  have hwf := wellformed_run (seed0 r remote) (seed0_wf r remote hr) t
  have hb := marker_bit1_all_times (seed0 r remote)
    (seed0_wf r remote hr) (seed0_marker1 r remote) t
  have hp := paint_run (seed0 r remote)
    (seed0_wf r remote hr) (seed0_marker1 r remote) t
  have he : run t (seed r remote) = paint c := by
    rw [←paint_seed0 r remote, hp]
  have ht' : terminal (run t (seed r remote)) = true := by
    rw [he, paint_terminal c hwf hb]
    exact ht
  have hh := terminal_classification r remote hr t ht'
  rw [he] at hh
  rcases hh with ⟨hpos, hstate, hcell⟩ | ⟨hstate, hscan⟩
  · left
    have hc : cell (paint c) 1 = cell c 1 := by
      simp [cell, paint, Nat.testBit_or,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
    exact ⟨hpos, hstate, by simpa only [hc] using hcell⟩
  · right
    exact ⟨hstate, by simpa only [paint_scan c hwf.2.2] using hscan⟩

#print axioms seed0_terminal_classification
end BB6.PhysicalWindow.ESeam

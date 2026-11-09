import PhysicalWindow
import ESeamTreeMaster

namespace BB6.PhysicalWindow.ESeam
open BB6.PhysicalWindow

private theorem eq_table (s bit : Nat) :
    table s bit = BB6.TreeCert.table s bit := rfl

private theorem eq_encode (off st bits : Nat) :
    encode off st bits = BB6.TreeCert.encode off st bits := rfl

private theorem eq_safe (v : Nat) :
    safe v = BB6.TreeCert.safe v := rfl

private theorem eq_successors (v : Nat) :
    successors v = BB6.TreeCert.successors v := rfl

private def accept (v : Nat) : Bool :=
  BB6.TreeCert.member BB6.TreeCert.root v

private theorem certificate : Certificate accept := by
  refine ⟨?_, ?_⟩
  · intro v hv
    change BB6.TreeCert.safe v = true
    exact BB6.TreeCert.safe_member v hv
  · intro v w hv he
    exact BB6.TreeCert.successor_closed v w hv (by simpa only [eq_successors] using he)

private theorem all_seeds (r : Nat) (hr : r < 128) :
    accept (encode 10 4 (171+2048*r)) = true := by
  change BB6.TreeCert.member BB6.TreeCert.root
    (BB6.TreeCert.encode 10 4 (171+2048*r)) = true
  exact BB6.TreeCert.seed_member r hr

/-- Kernel-certified finite invariant applied to a complete physical
    unbounded right tape. Any first protected-marker visit is C/1. -/
theorem original_e_base_marker_safe
    (r : Nat) (remote : Nat → Bool) (hr : r < 128) (t : Nat)
    (hm : (run t (seed r remote)).pos = 1) :
    (run t (seed r remote)).state = 2 ∧
      cell (run t (seed r remote)) 1 = true :=
  all_time_marker_safe accept certificate all_seeds r remote hr t hm

#print axioms original_e_base_marker_safe
end BB6.PhysicalWindow.ESeam

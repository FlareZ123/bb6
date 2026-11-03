import Boundary

namespace BB6.CryptidBoundaryShiftObstructions
open CryptidBoundary

/-!
A counterexample to extending the four-pair boundary conjugacy to
*all* alternating-stack lengths. The genuine F-prefix has stack
length 4*k+3; the low-stack cases below are synthetic inputs.
All evaluations use the unmodified, checksum-pinned six-state source.
-/

def eBoundary (m : Nat) : Cfg :=
  ⟨[false,false] ++ pairs m ++ [true,true], false, [], 4⟩

def physicalF0 (c : Cfg) : Bool :=
  (c.st == 5) && (!c.h) && c.l.isEmpty

theorem short_stack_halts :
    (run 11 (eBoundary 0)).st = 6 := by decide

theorem short_stack_no_prior_return :
    (List.range 11).all (fun t => !physicalF0 (run t (eBoundary 0))) = true := by
  decide

theorem four_extra_pairs_return :
    physicalF0 (run 19 (eBoundary 4)) = true := by decide

theorem four_extra_pairs_first_return :
    (List.range 19).all (fun t => !physicalF0 (run t (eBoundary 4))) = true := by
  decide

#print axioms short_stack_halts
#print axioms short_stack_no_prior_return
#print axioms four_extra_pairs_return
#print axioms four_extra_pairs_first_return

end BB6.CryptidBoundaryShiftObstructions

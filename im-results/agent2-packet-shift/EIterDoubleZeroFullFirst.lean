import Lean.Elab.Tactic.Omega
import EGenericFullFirst
import AIterDoubleZeroFirst

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EIterDoubleZeroFullFirst
open CryptidBoundary
open BB6.Agent2EGenericTurn
open BB6.Agent2EGenericFullFirst
open BB6.Agent2EAltBoundaryFirst

/-- First physically blank-left F/0 return on the entire unbounded
    E suffix family 0(10)^q (10)^(v+2) 110 (10)^r 0 Y.
    The included A turn has an interior F visit, but its left tape is
    physically nonblank; proof is kernel-audited on the original table.
    No premise of true-blank-root reachability is made. -/
theorem full_E_double_zero_first_physical
    (k q v r : Nat) (ys : List Bool) :
    let tmax := 12*k*k+49*k+(4*v+4*r+20)+48+4*q
    let start := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++
        (BB6.Agent2AIterDoubleZero.front v r ++ ys)))
    run tmax start =
      ⟨[],false,List.replicate (8*k+3) true ++
        outPacket q (BB6.Agent2AIterDoubleZero.out v r) ys,5⟩ ∧
    ∀ t, 0<t → t<tmax →
      ¬ Physical (run t start) := by
  exact full_E_from_noPhysical_turn_first
    k q (4*v+4*r+20)
    (BB6.Agent2AIterDoubleZero.front v r)
    (BB6.Agent2AIterDoubleZero.out v r) ys
    (fun L => BB6.Agent2AIterDoubleZero.a_double_zero_turn v r L ys)
    (fun L => BB6.Agent2AIterDoubleZeroFirst.a_double_zero_turn_noPhysical v r L ys)

#print axioms full_E_double_zero_first_physical
end BB6.Agent2EIterDoubleZeroFullFirst

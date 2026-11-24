import CryptidsFirstHolePaths

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6.Agent7FAR.R1Sibling
open BB6Coverage BB6.Cryptids608 BB6.Agent8TNFPath BB6.Agent8TNFPath.Cryptids
open BB6.Agent47WeightedHalt BB6.Agent13BlankDelay

/-- The r1 first-hole path with the final F/1 action changed from 1LF
    to 0LB. Erasing the original D/1 halt leaves exactly the proposed
    authentic sibling
    1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA0LB. -/
def r1SiblingMachine : Machine := fun s =>
  if s = (5, true) then some ⟨false, false, 1⟩ else expectedRLE_r1 s

def r1SiblingPartial : PartialMachine := forgetHaltRows r1SiblingMachine

/-- The same ten first-hole events reach this modified sibling: the altered
    F/1 transition is first queried at the final event, time 52. -/
theorem r1SiblingPathCheck :
    pathCheck r1SiblingMachine BB6.CoverageAdapter.firstOneCylinder 2 path_r1 = true := by
  decide

theorem r1SiblingReachable : FirstHolePath r1SiblingPartial 6 :=
  checked_from_root _ _ r1SiblingPathCheck

theorem r1SiblingD1Unassigned : r1SiblingPartial (3, true) = none := by
  decide

theorem r1SiblingF1Assigned :
    r1SiblingPartial (5, true) = some (some ⟨false, false, 1⟩) := by
  decide

theorem r1SiblingRootAction :
    r1SiblingPartial initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem r1SiblingSupport : TNFSupport r1SiblingPartial 6 := by
  decide

theorem r1SiblingNoAssignedHalt :
    weightedTNFNoAssignedHalt r1SiblingPartial := by
  decide

#print axioms r1SiblingReachable
#print axioms r1SiblingSupport
#print axioms r1SiblingNoAssignedHalt

end BB6.Agent7FAR.R1Sibling

import Raw140Long79
import BlockFARBridge
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Raw140Long
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
namespace X79
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,9,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X79
end Raw140Long

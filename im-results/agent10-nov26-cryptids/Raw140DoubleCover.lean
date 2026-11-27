import Raw140DoubleEntry
import BlockFARBridge
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Raw140Double
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
namespace X4
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,4,24]
theorem table_eq : BB6BlockFAR.partialTable M4 = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M4 m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X4
namespace X13
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,13,24]
theorem table_eq : BB6BlockFAR.partialTable M13 = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M13 m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X13
end Raw140Double

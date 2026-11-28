import Raw14042Positive
import BlockFARBridge
import ZipThreeHoleAudit

namespace Raw14042Cover
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,3,24]

theorem table_eq : BB6BlockFAR.partialTable M42 = p :=
  tableOK_sound _ _ (by decide)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M42 m (by rwa [table_eq]) Raw14042Positive.forever

theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))

#print axioms table_eq
#print axioms never
#print axioms cover
end Raw14042Cover

import Raw140Extra11
import BlockFARBridge
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Raw140Extra
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
namespace X11
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,16,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X11

end Raw140Extra

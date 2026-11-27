import Raw140Long34
import Raw140Long38
import Raw140Long75
import Raw140Long78
import BlockFARBridge
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Raw140Long
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
namespace X34
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,5,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X34

namespace X38
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,2,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X38

namespace X75
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,12,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X75

namespace X78
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,5,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X78
end Raw140Long

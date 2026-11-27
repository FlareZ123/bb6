import Raw140Extra00
import Raw140Extra01
import Raw140Extra02
import Raw140Extra03
import Raw140Extra04
import Raw140Extra05
import Raw140Extra06
import Raw140Extra07
import Raw140Extra08
import Raw140Extra09
import Raw140Extra10
import Raw140Extra11
import Raw140Extra12
import Raw140Extra13
import Raw140Extra14
import BlockFARBridge
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Raw140Extra
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
namespace X0
def p : PartialMachine := FAR.fromCodes [7,4,11,12,15,1,6,18,4,17,24,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X0

namespace X1
def p : PartialMachine := FAR.fromCodes [7,10,11,12,15,1,6,18,4,17,24,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X1

namespace X2
def p : PartialMachine := FAR.fromCodes [7,11,11,12,15,1,6,18,4,17,24,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X2

namespace X3
def p : PartialMachine := FAR.fromCodes [7,15,11,12,15,1,6,18,4,17,24,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X3

namespace X4
def p : PartialMachine := FAR.fromCodes [7,17,11,12,15,1,6,18,4,17,24,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X4

namespace X5
def p : PartialMachine := FAR.fromCodes [7,20,11,12,15,1,6,18,4,17,5,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X5

namespace X6
def p : PartialMachine := FAR.fromCodes [7,20,11,12,15,1,6,18,4,17,8,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X6

namespace X7
def p : PartialMachine := FAR.fromCodes [7,20,11,12,15,1,6,18,4,17,9,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X7

namespace X8
def p : PartialMachine := FAR.fromCodes [7,20,11,12,15,1,6,18,4,17,11,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X8

namespace X9
def p : PartialMachine := FAR.fromCodes [7,20,11,12,15,1,6,18,4,17,14,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X9

namespace X10
def p : PartialMachine := FAR.fromCodes [7,20,11,12,15,1,6,18,4,17,17,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X10

namespace X11
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,16,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X11

namespace X12
def p : PartialMachine := FAR.fromCodes [7,22,11,12,15,1,6,18,4,17,15,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X12

namespace X13
def p : PartialMachine := FAR.fromCodes [7,22,11,12,15,1,6,18,4,17,16,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X13

namespace X14
def p : PartialMachine := FAR.fromCodes [7,22,11,12,15,1,6,18,4,17,17,24]
theorem table_eq : BB6BlockFAR.partialTable M = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
end X14
end Raw140Extra

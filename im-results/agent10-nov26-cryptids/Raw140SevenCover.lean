import Raw140SevenEntry
import BlockFARBridge
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Raw140Orbit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
theorem never (v : Fin 7) (m : Machine) (hm : compatible (BB6BlockFAR.partialTable (variant v)) m) : NeverHalts m :=
  BB6BlockFAR.transfer_never (variant v) m hm (forever v)
namespace V0
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,4,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 0) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 0 m (by rwa [table_eq])
#print axioms never
end V0
namespace V1
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,8,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 1) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 1 m (by rwa [table_eq])
#print axioms never
end V1
namespace V2
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,1,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 2) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 2 m (by rwa [table_eq])
#print axioms never
end V2
namespace V3
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,16,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 3) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 3 m (by rwa [table_eq])
#print axioms never
end V3
namespace V4
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,6,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 4) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 4 m (by rwa [table_eq])
#print axioms never
end V4
namespace V5
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,3,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 5) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 5 m (by rwa [table_eq])
#print axioms never
end V5
namespace V6
def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,15,24]
theorem table_eq : BB6BlockFAR.partialTable (variant 6) = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Raw140Orbit.never 6 m (by rwa [table_eq])
#print axioms never
end V6
end Raw140Orbit

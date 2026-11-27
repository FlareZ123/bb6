import Box17AuditCore
import Box33DirectTree

namespace BB6.Agent13.Box33D17V21Cycles
open BB6Coverage BB6Coverage.Agent10ZipAudit
open Box17 (index decode)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def partialOf (codes : List (Fin 25)) : PartialMachine :=
  fun s => some (decode (codes.getD (index s).val 0))

def m3 : PartialMachine := partialOf [8,6,11,2,1,13,17,0,21,17,24,3]
theorem m3_check : zipCycle m3 2130 89 false (-33) = true := by decide
theorem m3_never (m : Machine) (hm : compatible m3 m) : NeverHalts m :=
  zipCycle_sound m3 2130 89 false (-33) (by decide) m3_check m hm
#print axioms m3_never

def m5 : PartialMachine := partialOf [8,2,11,12,1,13,17,0,21,17,24,3]
theorem m5_check : zipCycle m5 2482 103 false (-17) = true := by decide
theorem m5_never (m : Machine) (hm : compatible m5 m) : NeverHalts m :=
  zipCycle_sound m5 2482 103 false (-17) (by decide) m5_check m hm
#print axioms m5_never

def m7 : PartialMachine := partialOf [8,14,11,0,1,13,17,22,21,11,24,2]
theorem m7_check : zipCycle m7 2092 1630 true (26) = true := by decide
theorem m7_never (m : Machine) (hm : compatible m7 m) : NeverHalts m :=
  zipCycle_sound m7 2092 1630 true (26) (by decide) m7_check m hm
#print axioms m7_never

end BB6.Agent13.Box33D17V21Cycles

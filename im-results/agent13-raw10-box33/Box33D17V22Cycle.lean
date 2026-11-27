import Box17AuditCore
import Box33DirectTree

namespace BB6.Agent13.Box33D17V22Cycle
open BB6Coverage BB6Coverage.Agent10ZipAudit
open Box17 (index decode)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def partialTable : PartialMachine :=
  fun s => some (decode (([8,14,11,18,1,13,17,6,22,11,4,0] : List (Fin 25)).getD (index s).val 0))

-- The head moves from 56 to 66; throughout the period it stays at or above 51.
theorem checked : zipCycle partialTable 9078 444 true 51 = true := by decide
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m :=
  zipCycle_sound partialTable 9078 444 true 51 (by decide) checked m hm
#print axioms compatible_never
end BB6.Agent13.Box33D17V22Cycle

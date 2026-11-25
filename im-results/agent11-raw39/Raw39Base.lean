import ZipThreeHoleAudit
import Raw39Pumps00
import Raw39Pumps01
import Raw39Pumps02
import Raw39Pumps03
import Raw39Pumps04
import Raw39Pumps05
import Raw39Pumps06
import Raw39Pumps07
import Raw39Counter2391
import Raw39Counter2575
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev p1RB : PartialMachine := refine p39 (0,true) (some ⟨true,true,1⟩)
theorem p1RB_root : p1RB initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p1RB_nohalt : weightedTNFNoAssignedHalt p1RB :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev child39 (mv : Move) := refine p1RB (1,true) (some mv)
theorem query1RB : zipQueryOK 175 p1RB 7 (1,true) = true := by decide
theorem query39 : zipQueryOK 175 p39 6 (0,true) = true := by decide

end BB6.Agent11Raw39

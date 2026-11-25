import ZipThreeHoleAudit
import Raw39RCCounter38
import Raw39RCCounter39
import Raw39RCCounter107
import Raw39RCCounter383
import Raw39RCCounter508
import Raw39RCCounter809
import Raw39RCCounter1089
import Raw39RCCounter1108
import Raw39Hard56
import Raw39Hard194
import Raw39RCPumps00
import Raw39RCPumps01
import Raw39RCPumps02
import Raw39RCPumps03
import Raw39RCPumps04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev p0RC : PartialMachine := refine p39 (0,true) (some ⟨false,true,2⟩)
theorem p0RC_root : p0RC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p0RC_nohalt : weightedTNFNoAssignedHalt p0RC :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev childRC (mv : Move) := refine p0RC (2,true) (some mv)
theorem queryRC : zipQueryOK 2354 p0RC 7 (2,true) = true := by decide
theorem query39 : zipQueryOK 2354 p39 6 (0,true) = true := by decide

end BB6.Agent11Raw39RC

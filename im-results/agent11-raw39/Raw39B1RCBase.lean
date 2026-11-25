import ZipThreeHoleAudit
import Raw39B1RCCounter1058
import Raw39B1RCCounter1083
import Raw39B1RCCounter1843
import Raw39B1RCCounter2083
import Raw39B1RCCounter1896
import Raw39B1RCCounter2124
import Raw39B1RCCounter1964
import Raw39B1RCCounter2205
import Raw39B1RCPumps00
import Raw39B1RCPumps01
import Raw39B1RCPumps02
import Raw39B1RCPumps03
import Raw39B1RCPumps04
import Raw39B1RCPumps05
import Raw39B1RCPumps06
import Raw39B1RCPumps07
import Raw39B1RCPumps08
import Raw39B1RCPumps09
import Raw39B1RCPumps10
import Raw39B1RCPumps11
import Raw39B1RCPumps12
import Raw39B1RCPumps13
import Raw39B1RCPumps14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨true,true,2⟩)
theorem pChild_root : pChild initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pChild_nohalt : weightedTNFNoAssignedHalt pChild :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev child (mv : Move) := refine pChild (2,true) (some mv)
theorem queryChild : zipQueryOK 1882 pChild 7 (2,true) = true := by decide
theorem query39 : zipQueryOK 1882 p39 6 (0,true) = true := by decide

end BB6.Agent11Raw39B1RC

import ZipThreeHoleAudit
import Raw39B0RBCounter61
import Raw39B0RBCounter328
import Raw39B0RBCounter682
import Raw39B0RBCounter861
import Raw39B0RBCounter683
import Raw39B0RBCounter862
import Raw39B0RBCounter685
import Raw39B0RBCounter864
import Raw39B0RBCounter686
import Raw39B0RBCounter865
import Raw39B0RBPumps00
import Raw39B0RBPumps01
import Raw39B0RBPumps02
import Raw39B0RBPumps03
import Raw39B0RBPumps04
import Raw39B0RBPumps05
import Raw39B0RBPumps06
import Raw39B0RBPumps07
import Raw39B0RBPumps08
import Raw39B0RBPumps09
import Raw39B0RBPumps10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨false,true,1⟩)
theorem pChild_root : pChild initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pChild_nohalt : weightedTNFNoAssignedHalt pChild :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev child (mv : Move) := refine pChild (1,true) (some mv)
theorem queryChild : zipQueryOK 1271 pChild 7 (1,true) = true := by decide
theorem query39 : zipQueryOK 1271 p39 6 (0,true) = true := by decide

end BB6.Agent11Raw39B0RB

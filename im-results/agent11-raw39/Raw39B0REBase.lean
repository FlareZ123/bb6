import ZipThreeHoleAudit
import Raw39B0RECounter231
import Raw39B0RECounter234
import Raw39B0RECounter640
import Raw39B0RECounter641
import Raw39B0RECounter1948
import Raw39B0RECounter2293
import Raw39B0RECounter2294
import Raw39B0RECounter2295
import Raw39B0RECounter2481
import Raw39Stack468
import Raw39RE2172
import Raw39B0REPumps00
import Raw39B0REPumps01
import Raw39B0REPumps02
import Raw39B0REPumps03
import Raw39B0REPumps04
import Raw39B0REPumps05
import Raw39B0REPumps06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨false,true,4⟩)
theorem pChild_root : pChild initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pChild_nohalt : weightedTNFNoAssignedHalt pChild :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev child (mv : Move) := refine pChild (4,true) (some mv)
theorem queryChild : zipQueryOK 944 pChild 7 (4,true) = true := by decide
theorem query39 : zipQueryOK 944 p39 6 (0,true) = true := by decide

end BB6.Agent11Raw39B0RE

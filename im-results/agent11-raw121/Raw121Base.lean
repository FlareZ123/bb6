import ZipThreeHoleAudit
import Raw121Pumps
import Raw121Quadratic
import Raw121Counter
import Raw121QuadraticExtra
import Raw121BinaryA
import Raw121Exceptions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p121 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4, true) (some ⟨true, true, 4⟩)

theorem p121_root : p121 initialSlot = some (some ⟨true, true, 1⟩) := by decide

theorem p121_nohalt : weightedTNFNoAssignedHalt p121 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)

abbrev child121 (mv : Move) := refine p121 (4, false) (some mv)

theorem query121 : zipQueryOK 4063 p121 8 (4, false) = true := by decide

end BB6.Agent11Raw121

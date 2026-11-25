import Raw111Prefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

/-- Canonical-124 raw122 (canonical index86), E1=0LF, first hole F1. -/
abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,5⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev child (mv : Move) : PartialMachine := refine parent (5,true) (some mv)
end BB6.Agent43Raw122

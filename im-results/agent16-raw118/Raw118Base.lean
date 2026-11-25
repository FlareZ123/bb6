import Raw111Prefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw118
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,4⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev bound : Nat := 756496
theorem root_query : zipQueryOK bound parent 9 (4,false) = true := by decide
#print axioms root_query
end BB6.Agent16Raw118

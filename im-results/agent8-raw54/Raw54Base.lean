import Raw111Prefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
abbrev raw54 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,false,4⟩)
abbrev e1 : PartialMachine := refine raw54 (4,true) (some ⟨false,false,4⟩)
abbrev parent : PartialMachine := refine e1 (4,false) (some ⟨true,false,1⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)))
theorem raw54_query : zipQueryOK 7014 raw54 6 (4,true) = true := by decide
theorem e1_query : zipQueryOK 7014 e1 7 (4,false) = true := by decide
#print axioms parent_nohalt
#print axioms raw54_query
#print axioms e1_query
end BB6.Agent8Raw54

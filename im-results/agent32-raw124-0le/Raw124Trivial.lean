import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw124Trivial
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev p1LD : PartialMachine := refine parent (5,true) (some ⟨true,false,3⟩)
abbrev p1RE : PartialMachine := refine parent (5,true) (some ⟨true,true,4⟩)
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem bound1LD : ∀ m, compatible p1LD m → WeightedBound 7 m :=
  (certifiedZip 7 p1LD (.cycle 11 1 false (-1)) (by decide)
    (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt) (by decide)).sound
theorem bound1RE : ∀ m, compatible p1RE m → WeightedBound 7 m :=
  (certifiedZip 7 p1RE (.cycle 6 2 true 1) (by decide)
    (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt) (by decide)).sound
#print axioms bound1LD
#print axioms bound1RE
end BB6.Agent32Raw124Trivial

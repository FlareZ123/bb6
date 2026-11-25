import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6Raw57Easy
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p57 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,0⟩)
abbrev child (mv : Move) := refine p57 (0,true) (some mv)
theorem child_root (mv : Move) : child mv initialSlot = some (some ⟨true,true,1⟩) := by rfl
theorem child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (child mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))

noncomputable def la : WeightedTNFCertificate 273 (child ⟨false,false,0⟩) 6 :=
  certifiedZip 273 _ (.cycle 0 9 false 3) (child_root _) (child_nohalt _) (by decide)
noncomputable def rd : WeightedTNFCertificate 273 (child ⟨false,true,3⟩) 6 :=
  certifiedZip 273 _ (.cycle 13 1 false 1) (child_root _) (child_nohalt _) (by decide)
noncomputable def le : WeightedTNFCertificate 273 (child ⟨false,false,4⟩) 6 :=
  certifiedZip 273 _ (.cycle 0 9 false 3) (child_root _) (child_nohalt _) (by decide)
#print axioms la
#print axioms rd
#print axioms le
end BB6.Agent6Raw57Easy

import PartialAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw123
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

abbrev p123 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,5⟩)
theorem p123_root : p123 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p123_nohalt : weightedTNFNoAssignedHalt p123 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev child123 (mv : Move) := refine p123 (5,true) (some mv)
theorem query123 : zipQueryOK 10000 p123 7 (5,true) = true := by decide

def cut123 (kids : Move → PartialAudit) : PartialAudit := .split 7 (5,true) kids

theorem cut123_checked (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 10000 (child123 mv) (kids mv) = true) :
    partialCheck 10000 p123 (cut123 kids) = true := by
  change (zipQueryOK 10000 p123 7 (5,true) &&
    allMoves (fun mv => partialCheck 10000 (child123 mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query123, allMoves_of _ hk⟩

theorem cut123_sound (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 10000 (child123 mv) (kids mv) = true) :
    ∀ m, compatible p123 m → WeightedBound 10000 m ∨
      ∃ e ∈ partialResiduals p123 (cut123 kids), compatible e.2 m :=
  partialSound 10000 p123 (cut123 kids) p123_root p123_nohalt (cut123_checked kids hk)

theorem cover_of_cut123 (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 10000 (child123 mv) (kids mv) = true)
    (B : Nat) (hB : 10000 ≤ B)
    (hLeaves : ∀ e ∈ partialResiduals p123 (cut123 kids), Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p123 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases cut123_sound kids hk m hm with hb | ⟨e, he, hc⟩
  · intro k d h1 h2
    exact Nat.le_trans (hb k d h1 h2) hB
  · exact (hLeaves e he).sound m hc

#print axioms cut123_sound
#print axioms cover_of_cut123
end BB6.Agent7Raw123

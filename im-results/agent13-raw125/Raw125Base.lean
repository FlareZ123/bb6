import PartialAudit

set_option maxRecDepth 12900
set_option maxHeartbeats 0
namespace BB6.Agent13Raw125
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

abbrev p125 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,true,5⟩)
theorem p125_root : p125 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p125_nohalt : weightedTNFNoAssignedHalt p125 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev child125 (mv : Move) := refine p125 (5,true) (some mv)
theorem query125 : zipQueryOK 1290 p125 7 (5,true) = true := by decide

def cut125 (kids : Move → PartialAudit) : PartialAudit := .split 7 (5,true) kids

theorem cut125_checked (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 1290 (child125 mv) (kids mv) = true) :
    partialCheck 1290 p125 (cut125 kids) = true := by
  change (zipQueryOK 1290 p125 7 (5,true) &&
    allMoves (fun mv => partialCheck 1290 (child125 mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query125, allMoves_of _ hk⟩

theorem cut125_sound (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 1290 (child125 mv) (kids mv) = true) :
    ∀ m, compatible p125 m → WeightedBound 1290 m ∨
      ∃ e ∈ partialResiduals p125 (cut125 kids), compatible e.2 m :=
  partialSound 1290 p125 (cut125 kids) p125_root p125_nohalt (cut125_checked kids hk)

theorem cover_of_cut125 (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 1290 (child125 mv) (kids mv) = true)
    (B : Nat) (hB : 1290 ≤ B)
    (hLeaves : ∀ e ∈ partialResiduals p125 (cut125 kids), Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p125 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases cut125_sound kids hk m hm with hb | ⟨e, he, hc⟩
  · intro k d h1 h2
    exact Nat.le_trans (hb k d h1 h2) hB
  · exact (hLeaves e he).sound m hc

#print axioms cut125_sound
#print axioms cover_of_cut125
end BB6.Agent13Raw125

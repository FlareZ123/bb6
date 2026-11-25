import PartialAudit

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent13Raw38
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

abbrev p38 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,false,0⟩)
theorem p38_root : p38 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p38_nohalt : weightedTNFNoAssignedHalt p38 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev child38 (mv : Move) := refine p38 (0,true) (some mv)
theorem query38 : zipQueryOK 1000 p38 6 (0,true) = true := by decide

def cut38 (kids : Move → PartialAudit) : PartialAudit := .split 6 (0,true) kids

theorem cut38_checked (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 1000 (child38 mv) (kids mv) = true) :
    partialCheck 1000 p38 (cut38 kids) = true := by
  change (zipQueryOK 1000 p38 6 (0,true) &&
    allMoves (fun mv => partialCheck 1000 (child38 mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query38, allMoves_of _ hk⟩

theorem cut38_sound (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 1000 (child38 mv) (kids mv) = true) :
    ∀ m, compatible p38 m → WeightedBound 1000 m ∨
      ∃ e ∈ partialResiduals p38 (cut38 kids), compatible e.2 m :=
  partialSound 1000 p38 (cut38 kids) p38_root p38_nohalt (cut38_checked kids hk)

theorem cover_of_cut38 (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 1000 (child38 mv) (kids mv) = true)
    (B : Nat) (hB : 1000 ≤ B)
    (hLeaves : ∀ e ∈ partialResiduals p38 (cut38 kids), Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p38 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases cut38_sound kids hk m hm with hb | ⟨e, he, hc⟩
  · intro k d h1 h2
    exact Nat.le_trans (hb k d h1 h2) hB
  · exact (hLeaves e he).sound m hc

#print axioms cut38_sound
#print axioms cover_of_cut38
end BB6.Agent13Raw38

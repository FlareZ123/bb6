import ChampionF1OneLAIntegration
import Agent41F1ZeroRCCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6F1ZeroRCIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent47Canonical78
open BB6.Agent48F1Integration
open BB6.Agent48F1RFIntegration
open BB6.Agent48F1ZeroLFIntegration
open BB6.Agent6F1OneLAIntegration
open BB6Coverage.FAR

/-- The source-certified F/1=0RC parent is exactly the corresponding
    ordinary child of the fifth champion-path split. -/
theorem zeroRC_is_depth5_sibling :
    sameTable BB6.Agent41F1ZeroRC.parent
      (championChild 5 ⟨false,true,2⟩) = true := by
  decide

/-- Lift the exact source-accepted 3807 bound to the attained champion score. -/
theorem cover_zeroRC (B : Nat) (hB : 3807 ≤ B) :
    Cover (WeightedBound B) BB6.Agent41F1ZeroRC.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent41F1ZeroRC.all_completions_weighted m hm k d hk hd) hB

def parentZeroRC (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent41F1ZeroRC.parent

/-- Remove only the exact source-certified 0RC sibling. -/
noncomputable def remainingF1ZeroRC :
    List (List Move × PartialMachine) :=
  remainingF1OneLA.filter (fun e => !parentZeroRC e.2)

theorem zeroRC_parent_present :
    ∃ e ∈ remainingF1OneLA,
      sameTable e.2 BB6.Agent41F1ZeroRC.parent = true := by
  decide

theorem remainingF1ZeroRC_count : remainingF1ZeroRC.length = 106 := by
  decide

theorem removedZeroRC_count :
    remainingF1OneLA.length - remainingF1ZeroRC.length = 1 := by
  decide

/-- Every prior 107-leaf obligation is either the certified 0RC parent or
    remains explicitly in the 106-leaf frontier. -/
theorem cover_remainingF1OneLA
    (hLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1OneLA) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentZeroRC e.2 = true
  · have heq : e.2 = BB6.Agent41F1ZeroRC.parent := sameTable_sound h
    rw [heq]
    exact cover_zeroRC championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

/-- Conditional exactness after both 1LA and 0RC grafts: 77 other canonical
    representatives and 106 explicit raw139 leaves remain. -/
theorem exact_from_remainingF1ZeroRC
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  exact_from_remainingF1OneLA hOther
    (fun e he => cover_remainingF1OneLA hLeaves e he)

#print axioms zeroRC_is_depth5_sibling
#print axioms cover_zeroRC
#print axioms zeroRC_parent_present
#print axioms remainingF1ZeroRC_count
#print axioms removedZeroRC_count
#print axioms cover_remainingF1OneLA
#print axioms exact_from_remainingF1ZeroRC

end BB6.Agent6F1ZeroRCIntegration

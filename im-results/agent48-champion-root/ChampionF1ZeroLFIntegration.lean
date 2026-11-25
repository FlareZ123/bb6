import ChampionF1RFIntegration
import Agent41F1ZeroLFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent48F1ZeroLFIntegration

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration BB6.Agent41F0Extended BB6.Agent47Canonical78
open BB6.Agent48F1Integration BB6.Agent48F1RFIntegration

/-- The source-accepted 0LF parent is the exact F/1=0LF depth-five
    sibling on the champion path. -/
theorem zeroLF_is_depth5_sibling :
    sameTable BB6.Agent41F1ZeroLF.parent
      (championChild 5 ⟨false,false,5⟩) = true := by
  decide

/-- Lift the original-source 0LF bound 1603 to the attained champion score. -/
theorem cover_zeroLF (B : Nat) (hB : 1603 ≤ B) :
    Cover (WeightedBound B) BB6.Agent41F1ZeroLF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent41F1ZeroLF.all_completions_weighted m hm k d hk hd) hB

def parentZeroLF (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent41F1ZeroLF.parent

/-- Remove only the exact 0LF cylinder; all other raw139 obligations remain. -/
noncomputable def remainingF1ZeroLF :
    List (List Move × PartialMachine) :=
  BB6.Agent48F1RFIntegration.remainingF1RF.filter
    (fun e => !parentZeroLF e.2)

theorem zeroLF_parent_present :
    ∃ e ∈ BB6.Agent48F1RFIntegration.remainingF1RF,
      sameTable e.2 BB6.Agent41F1ZeroLF.parent = true := by
  decide

theorem remainingF1ZeroLF_count : remainingF1ZeroLF.length = 108 := by
  decide

theorem removedZeroLF_count :
    BB6.Agent48F1RFIntegration.remainingF1RF.length -
      remainingF1ZeroLF.length = 1 := by
  decide

/-- Every prior 109-leaf obligation is either the certified 0LF parent or
    remains explicitly in the 108-leaf frontier. -/
theorem cover_remainingF1RF
    (hLeaves : ∀ e ∈ remainingF1ZeroLF,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ BB6.Agent48F1RFIntegration.remainingF1RF) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentZeroLF e.2 = true
  · have heq : e.2 = BB6.Agent41F1ZeroLF.parent := sameTable_sound h
    rw [heq]
    exact cover_zeroLF championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

/-- Conditional exactness after the 0LF graft: 77 nonchampion canonical
    representatives and 108 explicit raw139 leaves remain. -/
theorem exact_from_remainingF1ZeroLF
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1ZeroLF,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent48F1RFIntegration.exact_from_remainingF1RF hOther
    (fun e he => cover_remainingF1RF hLeaves e he)

#print axioms zeroLF_is_depth5_sibling
#print axioms cover_zeroLF
#print axioms zeroLF_parent_present
#print axioms remainingF1ZeroLF_count
#print axioms removedZeroLF_count
#print axioms cover_remainingF1RF
#print axioms exact_from_remainingF1ZeroLF

end BB6.Agent48F1ZeroLFIntegration

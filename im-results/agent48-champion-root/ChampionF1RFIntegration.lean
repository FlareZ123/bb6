import ChampionF1SiblingIntegration
import ChampionF1ZeroRFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48F1RFIntegration
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration BB6.Agent41F0Extended BB6.Agent47Canonical78
open BB6Coverage.FAR BB6.Agent48F1Integration

theorem zeroRF_is_depth5_sibling :
    sameTable BB6.Agent48F1ZeroRF.parent (championChild 5 ⟨false,true,5⟩) = true := by
  decide
    championP1, championResidual, championRootAfterB, refine, root]

theorem cover_zeroRF (B : Nat) (hB : 211 ≤ B) :
    Cover (WeightedBound B) BB6.Agent48F1ZeroRF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent48F1ZeroRF.all_completions_weighted m hm k d hk hd) hB

def parentZeroRF (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent48F1ZeroRF.parent

noncomputable def remainingF1RF : List (List Move × PartialMachine) :=
  remainingF1Extended.filter (fun e => !parentZeroRF e.2)

theorem remainingF1RF_count : remainingF1RF.length = 109 := by decide

theorem cover_remainingF1Extended
    (hLeaves : ∀ e ∈ remainingF1RF, Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine) (he : e ∈ remainingF1Extended) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentZeroRF e.2 = true
  · have heq : e.2 = BB6.Agent48F1ZeroRF.parent := sameTable_sound h
    rw [heq]
    exact cover_zeroRF championScore (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

theorem exact_from_remainingF1RF
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1RF, Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  exact_from_remainingF1Extended hOther
    (fun e he => cover_remainingF1Extended hLeaves e he)

#print axioms zeroRF_is_depth5_sibling
#print axioms cover_zeroRF
#print axioms remainingF1RF_count
#print axioms cover_remainingF1Extended
#print axioms exact_from_remainingF1RF
end BB6.Agent48F1RFIntegration

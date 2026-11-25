import F0SiblingIntegration
import Champion0RACover
import ChampionRemainingCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent41F0Extended

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual BB6.Agent31ChampionParentIntegration
open BB6.Agent6F0 BB6.Agent6F0.AFirst
open BB6.Agent6F0.Integration
open BB6.Agent47Canonical78

/-- Parent tables with newly source-accepted Agent48 covers. -/
def parentZeroRA (p : PartialMachine) : Bool :=
  sameTable p (parent ⟨false,true,0⟩)

def parentZeroRC (p : PartialMachine) : Bool :=
  sameTable p (parent ⟨false,true,2⟩)

def parentOneRE (p : PartialMachine) : Bool :=
  sameTable p (parent ⟨true,true,4⟩)

/-- Remove the unconditional 0RA parent and replace the conditional 0RC and
    1RE parents by their single hard one-hole children. The ten previously
    certified F/0 siblings remain removed by closedF0. -/
def refineResidual (e : List Move × PartialMachine) :
    Option (List Move × PartialMachine) :=
  if closedF0 e.2 then none
  else if parentZeroRA e.2 then none
  else if parentZeroRC e.2 then
    some (e.1 ++ [⟨false,true,3⟩],
      childA ⟨false,true,2⟩ ⟨false,true,3⟩)
  else if parentOneRE e.2 then
    some (e.1 ++ [⟨false,true,3⟩],
      child ⟨true,true,4⟩ ⟨false,true,3⟩)
  else some e

noncomputable def remainingExtended :
    List (List Move × PartialMachine) :=
  championResidualFrontierWithParentResiduals.filterMap refineResidual

theorem remainingExtended_count : remainingExtended.length = 112 := by
  decide

theorem refined_residual_cover
    (hLeaves : ∀ e ∈ remainingExtended,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual := by
  apply cover_of_championResidual_frontier
  intro e he
  by_cases hc : closedF0 e.2 = true
  · exact cover_closed championScore champion_score_ge_49394 e.2 hc
  · by_cases hRA : parentZeroRA e.2 = true
    · rw [sameTable_sound hRA]
      exact BB6.Agent48RA.cover_zeroRA championScore (by omega)
    · by_cases hRC : parentZeroRC e.2 = true
      · have hChild :
            (e.1 ++ [⟨false,true,3⟩],
              childA ⟨false,true,2⟩ ⟨false,true,3⟩) ∈ remainingExtended := by
          unfold remainingExtended
          apply List.mem_filterMap.mpr
          refine ⟨e, he, ?_⟩
          simp [refineResidual, parentZeroRA, parentZeroRC, parentOneRE,
            hc, hRA, hRC]
        rw [sameTable_sound hRC]
        exact BB6.Agent48Remaining.cover_zeroRC_of_RD championScore
          (by omega) (hLeaves _ hChild)
      · by_cases hRE : parentOneRE e.2 = true
        · have hChild :
              (e.1 ++ [⟨false,true,3⟩],
                child ⟨true,true,4⟩ ⟨false,true,3⟩) ∈ remainingExtended := by
            unfold remainingExtended
            apply List.mem_filterMap.mpr
            refine ⟨e, he, ?_⟩
            simp [refineResidual, parentZeroRA, parentZeroRC, parentOneRE,
              hc, hRA, hRC, hRE]
          rw [sameTable_sound hRE]
          exact BB6.Agent48Remaining.cover_oneRE_of_RD championScore
            (by omega) (hLeaves _ hChild)
        · have hMem : e ∈ remainingExtended := by
            unfold remainingExtended
            apply List.mem_filterMap.mpr
            refine ⟨e, he, ?_⟩
            simp [refineResidual, parentZeroRA, parentZeroRC, parentOneRE,
              hc, hRA, hRC, hRE]
          exact hLeaves e hMem

theorem exact_from_remainingExtended
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingExtended,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore := by
  apply BB6.Agent47Canonical78.exact_at_target championScore
    (Nat.le_of_lt BB6.Agent31Canonical78Exact.champion_score_gt_7014)
  · intro e he
    by_cases hEq : e.2 = championResidual
    · simpa [hEq] using refined_residual_cover hLeaves
    · exact hOther e he hEq
  · exact BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms remainingExtended_count
#print axioms refined_residual_cover
#print axioms exact_from_remainingExtended

end BB6.Agent41F0Extended

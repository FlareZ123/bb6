import ChampionF1ZeroRBZeroLAOneRDIntegration
import Agent14OneLBCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6F1OneLBIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent47Canonical78
open BB6.Agent41F1ZeroRBZeroLAOneRDIntegration
open BB6Coverage.FAR

theorem oneLB_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLB.parent
      (championChild 5 ⟨true,false,1⟩) = true := by decide

theorem cover_oneLB (B : Nat) (hB : 172 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneLB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLB.all_completions_weighted m hm k d hk hd) hB

def parentOneLB (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneLB.parent

noncomputable def remainingF1AfterZeroRBZeroLAOneRDOneLB :
    List (List Move × PartialMachine) :=
  BB6.Agent41F1ZeroRBZeroLAOneRDIntegration.remainingF1AfterZeroRBZeroLAOneRD.filter
    (fun e => !parentOneLB e.2)

theorem oneLB_parent_present :
    ∃ e ∈ BB6.Agent41F1ZeroRBZeroLAOneRDIntegration.remainingF1AfterZeroRBZeroLAOneRD,
      sameTable e.2 BB6.Agent14F1OneLB.parent = true := by decide

theorem remainingF1AfterZeroRBZeroLAOneRDOneLB_count :
    remainingF1AfterZeroRBZeroLAOneRDOneLB.length = 102 := by decide

theorem removedOneLB_count :
    BB6.Agent41F1ZeroRBZeroLAOneRDIntegration.remainingF1AfterZeroRBZeroLAOneRD.length -
      remainingF1AfterZeroRBZeroLAOneRDOneLB.length = 1 := by decide

theorem cover_remainingF1AfterZeroRBZeroLAOneRD
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLB,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ BB6.Agent41F1ZeroRBZeroLAOneRDIntegration.remainingF1AfterZeroRBZeroLAOneRD) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentOneLB e.2 = true
  · have heq : e.2 = BB6.Agent14F1OneLB.parent := sameTable_sound h
    rw [heq]
    exact cover_oneLB championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [parentOneLB, h]⟩

theorem exact_from_canonical77_and_raw139_four_sibling_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLB,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent41F1ZeroRBZeroLAOneRDIntegration.exact_from_canonical77_and_raw139_three_sibling_leaves
    hOther (fun e he => cover_remainingF1AfterZeroRBZeroLAOneRD hLeaves e he)

noncomputable def refinedCanonical77RosterAfterZeroRBZeroLAOneRDOneLB :
    List (List Move × PartialMachine) :=
  (BB6.Agent47CanonicalRaw114Accepted.roster.filter
    (fun e => !sameTable e.2 championResidual)) ++
  (remainingF1AfterZeroRBZeroLAOneRDOneLB.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem refinedCanonical77RosterAfterZeroRBZeroLAOneRDOneLB_count :
    refinedCanonical77RosterAfterZeroRBZeroLAOneRDOneLB.length = 178 := by decide

#print axioms oneLB_is_depth5_sibling
#print axioms cover_oneLB
#print axioms oneLB_parent_present
#print axioms remainingF1AfterZeroRBZeroLAOneRDOneLB_count
#print axioms removedOneLB_count
#print axioms cover_remainingF1AfterZeroRBZeroLAOneRD
#print axioms exact_from_canonical77_and_raw139_four_sibling_leaves
#print axioms refinedCanonical77RosterAfterZeroRBZeroLAOneRDOneLB_count
#print axioms BB6.Agent14F1OneLB.all_completions_weighted

end BB6.Agent6F1OneLBIntegration

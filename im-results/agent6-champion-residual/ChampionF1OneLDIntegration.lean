import ChampionF1OneLBIntegration
import Agent14OneLDCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14F1OneLDIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent47Canonical78
open BB6.Agent6F1OneLBIntegration
open BB6Coverage.FAR

theorem oneLD_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLD.parent
      (championChild 5 ⟨true,false,3⟩) = true := by decide

theorem cover_oneLD (B : Nat) (hB : 264 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneLD.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLD.all_completions_weighted m hm k d hk hd) hB

def parentOneLD (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneLD.parent

noncomputable def remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD :
    List (List Move × PartialMachine) :=
  BB6.Agent6F1OneLBIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLB.filter
    (fun e => !parentOneLD e.2)

theorem oneLD_parent_present :
    ∃ e ∈ BB6.Agent6F1OneLBIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLB,
      sameTable e.2 BB6.Agent14F1OneLD.parent = true := by decide

theorem remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD_count :
    remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD.length = 101 := by decide

theorem removedOneLD_count :
    BB6.Agent6F1OneLBIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLB.length -
      remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD.length = 1 := by decide

theorem cover_remainingF1AfterZeroRBZeroLAOneRDOneLB
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ BB6.Agent6F1OneLBIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLB) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentOneLD e.2 = true
  · have heq : e.2 = BB6.Agent14F1OneLD.parent := sameTable_sound h
    rw [heq]
    exact cover_oneLD championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [parentOneLD, h]⟩

theorem exact_from_canonical77_and_raw139_five_sibling_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent6F1OneLBIntegration.exact_from_canonical77_and_raw139_four_sibling_leaves
    hOther (fun e he => cover_remainingF1AfterZeroRBZeroLAOneRDOneLB hLeaves e he)

noncomputable def refinedCanonical77RosterAfterOneLD :
    List (List Move × PartialMachine) :=
  BB6.Agent6F1OneLBIntegration.refinedCanonical77RosterAfterZeroRBZeroLAOneRDOneLB.filter
    (fun e => !parentOneLD e.2)

theorem refinedCanonical77RosterAfterOneLD_count :
    refinedCanonical77RosterAfterOneLD.length = 177 := by decide

#print axioms oneLD_is_depth5_sibling
#print axioms cover_oneLD
#print axioms oneLD_parent_present
#print axioms remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD_count
#print axioms removedOneLD_count
#print axioms cover_remainingF1AfterZeroRBZeroLAOneRDOneLB
#print axioms exact_from_canonical77_and_raw139_five_sibling_leaves
#print axioms refinedCanonical77RosterAfterOneLD_count
#print axioms BB6.Agent14F1OneLD.all_completions_weighted

end BB6.Agent14F1OneLDIntegration

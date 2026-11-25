import ChampionF1OneLDIntegration
import Agent14OneRFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14F1OneRFIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent47Canonical78
open BB6.Agent14F1OneLDIntegration
open BB6Coverage.FAR

theorem oneRF_is_depth5_sibling :
    sameTable BB6.Agent14F1OneRF.parent
      (championChild 5 ⟨true,true,5⟩) = true := by decide

theorem cover_oneRF (B : Nat) (hB : 5423 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneRF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneRF.all_completions_weighted m hm k d hk hd) hB

def parentOneRF (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneRF.parent

noncomputable def remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF :
    List (List Move × PartialMachine) :=
  BB6.Agent14F1OneLDIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD.filter
    (fun e => !parentOneRF e.2)

theorem oneRF_parent_present :
    ∃ e ∈ BB6.Agent14F1OneLDIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD,
      sameTable e.2 BB6.Agent14F1OneRF.parent = true := by decide

theorem remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF_count :
    remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF.length = 100 := by decide

theorem removedOneRF_count :
    BB6.Agent14F1OneLDIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD.length -
      remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF.length = 1 := by decide

theorem cover_remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ BB6.Agent14F1OneLDIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentOneRF e.2 = true
  · have heq : e.2 = BB6.Agent14F1OneRF.parent := sameTable_sound h
    rw [heq]
    exact cover_oneRF championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [parentOneRF, h]⟩

theorem exact_from_canonical77_and_raw139_six_sibling_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent14F1OneLDIntegration.exact_from_canonical77_and_raw139_five_sibling_leaves
    hOther (fun e he => cover_remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD hLeaves e he)

noncomputable def refinedCanonical77RosterAfterOneLDOneRF :
    List (List Move × PartialMachine) :=
  BB6.Agent14F1OneLDIntegration.refinedCanonical77RosterAfterOneLD.filter
    (fun e => !parentOneRF e.2)

theorem refinedCanonical77RosterAfterOneLDOneRF_count :
    refinedCanonical77RosterAfterOneLDOneRF.length = 176 := by decide

#print axioms oneRF_is_depth5_sibling
#print axioms cover_oneRF
#print axioms oneRF_parent_present
#print axioms remainingF1AfterZeroRBZeroLAOneRDOneLBOneLDOneRF_count
#print axioms removedOneRF_count
#print axioms cover_remainingF1AfterZeroRBZeroLAOneRDOneLBOneLD
#print axioms exact_from_canonical77_and_raw139_six_sibling_leaves
#print axioms refinedCanonical77RosterAfterOneLDOneRF_count
#print axioms BB6.Agent14F1OneRF.all_completions_weighted

end BB6.Agent14F1OneRFIntegration

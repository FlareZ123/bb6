/-
DRAFT: 0RB parent-to-frontier consumer; not source-compiled.
-/
import ChampionResidualCanonical77Integration
import Agent41F1ZeroRBCover
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent41F1ZeroRBIntegration
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
open BB6.Agent6F1ZeroRCIntegration
open BB6.Agent6Canonical77ChampionIntegration
open BB6.Agent47CanonicalRefinement
open BB6Coverage.FAR

theorem zeroRB_is_depth5_sibling :
    sameTable BB6.Agent41F1ZeroRB.parent
      (championChild 5 ⟨false,true,1⟩) = true := by decide

theorem cover_zeroRB (B : Nat) (hB : 290 ≤ B) :
    Cover (WeightedBound B) BB6.Agent41F1ZeroRB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent41F1ZeroRB.all_completions_weighted m hm k d hk hd) hB

def parentZeroRB (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent41F1ZeroRB.parent

noncomputable def remainingF1ZeroRB :
    List (List Move × PartialMachine) :=
  BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC.filter
    (fun e => !parentZeroRB e.2)

theorem zeroRB_parent_present :
    ∃ e ∈ BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC,
      sameTable e.2 BB6.Agent41F1ZeroRB.parent = true := by decide

theorem remainingF1ZeroRB_count : remainingF1ZeroRB.length = 105 := by decide

theorem removedZeroRB_count :
    BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC.length -
      remainingF1ZeroRB.length = 1 := by decide

theorem cover_remainingF1ZeroRC
    (hLeaves : ∀ e ∈ remainingF1ZeroRB,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentZeroRB e.2 = true
  · have heq : e.2 = BB6.Agent41F1ZeroRB.parent := sameTable_sound h
    rw [heq]
    exact cover_zeroRB championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

theorem exact_from_canonical77_and_raw139_zeroRB_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1ZeroRB,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent6Canonical77ChampionIntegration.exact_from_canonical77_and_raw139_leaves
    hOther (fun e he => cover_remainingF1ZeroRC hLeaves e he)

noncomputable def refinedCanonical77RosterZeroRB :
    List (List Move × PartialMachine) :=
  (BB6.Agent47CanonicalRaw114Accepted.roster.filter
    (fun e => !sameTable e.2 championResidual)) ++
  (remainingF1ZeroRB.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem refinedCanonical77RosterZeroRB_count :
    refinedCanonical77RosterZeroRB.length = 181 := by decide

#print axioms zeroRB_is_depth5_sibling
#print axioms cover_zeroRB
#print axioms zeroRB_parent_present
#print axioms remainingF1ZeroRB_count
#print axioms removedZeroRB_count
#print axioms cover_remainingF1ZeroRC
#print axioms exact_from_canonical77_and_raw139_zeroRB_leaves
#print axioms refinedCanonical77RosterZeroRB_count
end BB6.Agent41F1ZeroRBIntegration

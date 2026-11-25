/-
DRAFT: source-accepted 0RB, 0LA, and 1RD sibling covers grafted into the
106-leaf raw139 F/1 residual. This is a consumer integration draft, not yet
source-compiled. If the finite membership/count proofs reduce as expected,
three distinct parent cylinders are removed, leaving 103 leaves.
-/
import ChampionResidualCanonical77Integration
import Agent41F1ZeroRBCover
import Agent14OneLACover
import Agent14OneRDCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent41F1ZeroRBZeroLAOneRDIntegration

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

theorem zeroLA_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLA.parent
      (championChild 5 ⟨false,false,0⟩) = true := by decide

theorem oneRD_is_depth5_sibling :
    sameTable BB6.Agent14F1OneRD.parent
      (championChild 5 ⟨true,true,3⟩) = true := by decide

theorem cover_zeroRB (B : Nat) (hB : 290 ≤ B) :
    Cover (WeightedBound B) BB6.Agent41F1ZeroRB.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent41F1ZeroRB.all_completions_weighted m hm k d hk hd) hB

theorem cover_zeroLA (B : Nat) (hB : 553 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneLA.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLA.all_completions_weighted m hm k d hk hd) hB

theorem cover_oneRD (B : Nat) (hB : 489 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneRD.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneRD.all_completions_weighted m hm k d hk hd) hB

def parentZeroRB (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent41F1ZeroRB.parent

def parentZeroLA (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneLA.parent

def parentOneRD (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneRD.parent

def removedF1Sibling (p : PartialMachine) : Bool :=
  parentZeroRB p || parentZeroLA p || parentOneRD p

noncomputable def remainingF1AfterZeroRBZeroLAOneRD :
    List (List Move × PartialMachine) :=
  BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC.filter
    (fun e => !removedF1Sibling e.2)

theorem zeroRB_parent_present :
    ∃ e ∈ BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC,
      sameTable e.2 BB6.Agent41F1ZeroRB.parent = true := by decide

theorem zeroLA_parent_present :
    ∃ e ∈ BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14F1OneLA.parent = true := by decide

theorem oneRD_parent_present :
    ∃ e ∈ BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14F1OneRD.parent = true := by decide

theorem remainingF1AfterZeroRBZeroLAOneRD_count :
    remainingF1AfterZeroRBZeroLAOneRD.length = 103 := by decide

theorem removedThreeParents_count :
    BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC.length -
      remainingF1AfterZeroRBZeroLAOneRD.length = 3 := by decide

theorem cover_remainingF1ZeroRC
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRD,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ BB6.Agent6F1ZeroRCIntegration.remainingF1ZeroRC) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases hRB : parentZeroRB e.2 = true
  · have heq : e.2 = BB6.Agent41F1ZeroRB.parent := sameTable_sound hRB
    rw [heq]
    exact cover_zeroRB championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · by_cases hLA : parentZeroLA e.2 = true
    · have heq : e.2 = BB6.Agent14F1OneLA.parent := sameTable_sound hLA
      rw [heq]
      exact cover_zeroLA championScore
        (Nat.le_trans (by decide) champion_score_ge_49394)
    · by_cases hRD : parentOneRD e.2 = true
      · have heq : e.2 = BB6.Agent14F1OneRD.parent := sameTable_sound hRD
        rw [heq]
        exact cover_oneRD championScore
          (Nat.le_trans (by decide) champion_score_ge_49394)
      · apply hLeaves e
        apply List.mem_filter.mpr
        exact ⟨he, by simp [removedF1Sibling, parentZeroRB, parentZeroLA, parentOneRD, hRB, hLA, hRD]⟩

theorem exact_from_canonical77_and_raw139_three_sibling_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRD,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent6Canonical77ChampionIntegration.exact_from_canonical77_and_raw139_leaves
    hOther (fun e he => cover_remainingF1ZeroRC hLeaves e he)

noncomputable def refinedCanonical77RosterAfterZeroRBZeroLAOneRD :
    List (List Move × PartialMachine) :=
  (BB6.Agent47CanonicalRaw114Accepted.roster.filter
    (fun e => !sameTable e.2 championResidual)) ++
  (remainingF1AfterZeroRBZeroLAOneRD.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem refinedCanonical77RosterAfterZeroRBZeroLAOneRD_count :
    refinedCanonical77RosterAfterZeroRBZeroLAOneRD.length = 179 := by decide

#print axioms zeroRB_is_depth5_sibling
#print axioms zeroLA_is_depth5_sibling
#print axioms oneRD_is_depth5_sibling
#print axioms cover_zeroRB
#print axioms cover_zeroLA
#print axioms cover_oneRD
#print axioms zeroRB_parent_present
#print axioms zeroLA_parent_present
#print axioms oneRD_parent_present
#print axioms remainingF1AfterZeroRBZeroLAOneRD_count
#print axioms removedThreeParents_count
#print axioms cover_remainingF1ZeroRC
#print axioms exact_from_canonical77_and_raw139_three_sibling_leaves
#print axioms refinedCanonical77RosterAfterZeroRBZeroLAOneRD_count

end BB6.Agent41F1ZeroRBZeroLAOneRDIntegration

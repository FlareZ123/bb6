import ChampionF1ZeroRCIntegration
import Agent14OneLDCover
import Agent14OneRFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6F1OneLDOneRFIntegration

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
open BB6Coverage.FAR

/-- The source-certified F/1=1LD parent is exactly the depth-five
    ordinary child reached after the champion's F/1 first hole. -/
theorem oneLD_is_depth5_sibling :
    sameTable BB6.Agent14F1OneLD.parent
      (championChild 5 ⟨true,false,3⟩) = true := by
  decide

/-- Lift the original-source 264 bound to the attained champion score. -/
theorem cover_oneLD (B : Nat) (hB : 264 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneLD.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneLD.all_completions_weighted m hm k d hk hd) hB

def parentOneLD (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneLD.parent

/-- Remove only the exact source-certified 1LD sibling. -/
noncomputable def remainingF1OneLD :
    List (List Move × PartialMachine) :=
  remainingF1ZeroRC.filter (fun e => !parentOneLD e.2)

theorem oneLD_parent_present :
    ∃ e ∈ remainingF1ZeroRC,
      sameTable e.2 BB6.Agent14F1OneLD.parent = true := by
  decide

theorem remainingF1OneLD_count : remainingF1OneLD.length = 105 := by
  decide

theorem removedOneLD_count :
    remainingF1ZeroRC.length - remainingF1OneLD.length = 1 := by
  decide

/-- Every 0RC-stage leaf is either the certified 1LD parent or remains
    explicitly in the 105-leaf frontier. -/
theorem cover_remainingF1ZeroRC
    (hLeaves : ∀ e ∈ remainingF1OneLD,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1ZeroRC) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentOneLD e.2 = true
  · have heq : e.2 = BB6.Agent14F1OneLD.parent := sameTable_sound h
    rw [heq]
    exact cover_oneLD championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

/-- The source-certified F/1=1RF parent is the second exact depth-five
    sibling consumed from the same champion-path first-hole split. -/
theorem oneRF_is_depth5_sibling :
    sameTable BB6.Agent14F1OneRF.parent
      (championChild 5 ⟨true,true,5⟩) = true := by
  decide

/-- Lift the original-source 5423 bound to the attained champion score. -/
theorem cover_oneRF (B : Nat) (hB : 5423 ≤ B) :
    Cover (WeightedBound B) BB6.Agent14F1OneRF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent14F1OneRF.all_completions_weighted m hm k d hk hd) hB

def parentOneRF (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent14F1OneRF.parent

/-- Remove only the exact source-certified 1RF sibling after the 1LD graft. -/
noncomputable def remainingF1OneRF :
    List (List Move × PartialMachine) :=
  remainingF1OneLD.filter (fun e => !parentOneRF e.2)

theorem oneRF_parent_present :
    ∃ e ∈ remainingF1OneLD,
      sameTable e.2 BB6.Agent14F1OneRF.parent = true := by
  decide

theorem remainingF1OneRF_count : remainingF1OneRF.length = 104 := by
  decide

theorem removedOneRF_count :
    remainingF1OneLD.length - remainingF1OneRF.length = 1 := by
  decide

/-- Every 1LD-stage leaf is either the certified 1RF parent or remains
    explicitly in the 104-leaf frontier. -/
theorem cover_remainingF1OneLD
    (hLeaves : ∀ e ∈ remainingF1OneRF,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1OneLD) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentOneRF e.2 = true
  · have heq : e.2 = BB6.Agent14F1OneRF.parent := sameTable_sound h
    rw [heq]
    exact cover_oneRF championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

/-- Conditional exactness after both newly source-accepted siblings:
    77 non-champion canonical representatives and 104 explicit raw139
    residual cylinders remain as the only Cover obligations. -/
theorem exact_from_remainingF1OneLDOneRF
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1OneRF,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  exact_from_remainingF1ZeroRC hOther
    (fun e he =>
      cover_remainingF1ZeroRC
        (fun e he => cover_remainingF1OneLD hLeaves e he) e he)

#print axioms BB6.Agent14F1OneLD.checked
#print axioms BB6.Agent14F1OneLD.all_completions_weighted
#print axioms BB6.Agent14F1OneRF.checked
#print axioms BB6.Agent14F1OneRF.all_completions_weighted
#print axioms oneLD_is_depth5_sibling
#print axioms cover_oneLD
#print axioms oneLD_parent_present
#print axioms remainingF1OneLD_count
#print axioms removedOneLD_count
#print axioms cover_remainingF1ZeroRC
#print axioms oneRF_is_depth5_sibling
#print axioms cover_oneRF
#print axioms oneRF_parent_present
#print axioms remainingF1OneRF_count
#print axioms removedOneRF_count
#print axioms cover_remainingF1OneLD
#print axioms exact_from_remainingF1OneLDOneRF

end BB6.Agent6F1OneLDOneRFIntegration

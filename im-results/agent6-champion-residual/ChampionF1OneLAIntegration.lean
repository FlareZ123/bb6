import ChampionF1ZeroLFIntegration
import ChampionF1OneLACover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6F1OneLAIntegration

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
open BB6Coverage.FAR

/-- The source-certified F/1=1LA parent is exactly the corresponding
    ordinary child of the fifth champion-path split. -/
theorem oneLA_is_depth5_sibling :
    sameTable BB6.Agent48F1OneLA.parent
      (championChild 5 ⟨true,false,0⟩) = true := by
  decide

/-- Lift the exact source-accepted 290 bound to the attained champion score. -/
theorem cover_oneLA (B : Nat) (hB : 290 ≤ B) :
    Cover (WeightedBound B) BB6.Agent48F1OneLA.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent48F1OneLA.all_completions_weighted m hm k d hk hd) hB

def parentOneLA (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent48F1OneLA.parent

/-- Remove only the exact source-certified 1LA sibling. -/
noncomputable def remainingF1OneLA :
    List (List Move × PartialMachine) :=
  remainingF1ZeroLF.filter (fun e => !parentOneLA e.2)

theorem oneLA_parent_present :
    ∃ e ∈ remainingF1ZeroLF,
      sameTable e.2 BB6.Agent48F1OneLA.parent = true := by
  decide

theorem remainingF1OneLA_count : remainingF1OneLA.length = 107 := by
  decide

theorem removedOneLA_count :
    remainingF1ZeroLF.length - remainingF1OneLA.length = 1 := by
  decide

/-- Every prior 108-leaf obligation is either the certified 1LA parent or
    remains explicitly in the 107-leaf frontier. -/
theorem cover_remainingF1ZeroLF
    (hLeaves : ∀ e ∈ remainingF1OneLA,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1ZeroLF) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : parentOneLA e.2 = true
  · have heq : e.2 = BB6.Agent48F1OneLA.parent := sameTable_sound h
    rw [heq]
    exact cover_oneLA championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · apply hLeaves e
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

/-- Conditional exactness after the 1LA graft: 77 other canonical
    representatives and 107 explicit raw139 leaves remain. -/
theorem exact_from_remainingF1OneLA
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1OneLA,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  exact_from_remainingF1ZeroLF hOther
    (fun e he => cover_remainingF1ZeroLF hLeaves e he)

#print axioms oneLA_is_depth5_sibling
#print axioms cover_oneLA
#print axioms oneLA_parent_present
#print axioms remainingF1OneLA_count
#print axioms removedOneLA_count
#print axioms cover_remainingF1ZeroLF
#print axioms exact_from_remainingF1OneLA

end BB6.Agent6F1OneLAIntegration

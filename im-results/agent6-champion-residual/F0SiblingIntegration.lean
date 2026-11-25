import ChampionResidualParentIntegration
import F0Counter0LE
import F0SiblingLong
import F0Counter1RD
import F0SiblingA
import F0Sibling1RB

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6F0.Integration

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster BB6.Agent13MixedBound109
open BB6ChampionArithmetic BB6Coverage.Agent48DirectRoot

theorem base_eq_championP6 : BB6.Agent6F0.base = championP6 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases b <;> rfl

theorem parent_eq_championChild (f : Move) :
    BB6.Agent6F0.parent f = championChild 6 f := by
  unfold BB6.Agent6F0.parent championChild
  rw [base_eq_championP6]
  rfl

/-- The first increment alone supplies a sufficient lower bound on the
    already attained champion score, without evaluating any large tower. -/
theorem champion_score_ge_49394 : 49394 ≤ championScore := by
  have hfirst : 49394 ≤ (sectionResult 7 2 6 63).cost := by
    change 49394 ≤ proposedIncrementCost (2%3) 7 6 63 +
      (sectionResult 6 (nextMarker 2) (nextExponent 2 6 63) (nextRight 63)).cost
    have hcost : 49394 ≤ proposedIncrementCost (2%3) 7 6 63 := by decide
    omega
  change 49394 ≤ proposedTM63Moves + 7
  rw [← threeSectionMoves_root]
  simp only [threeSectionMoves]
  omega

def closedMoves : List Move :=
  [⟨true,false,0⟩, ⟨true,false,4⟩, ⟨false,false,1⟩,
   ⟨true,false,2⟩, ⟨false,false,2⟩, ⟨true,true,2⟩,
   ⟨false,false,4⟩, ⟨true,true,3⟩, ⟨true,false,3⟩, ⟨true,true,1⟩]

theorem cover_move (B : Nat) (hB : 49394 ≤ B) (f : Move)
    (hf : f ∈ closedMoves) : Cover (WeightedBound B) (BB6.Agent6F0.parent f) := by
  simp only [closedMoves,List.mem_cons,List.mem_singleton] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h <;> subst f
  · exact BB6.Agent6F0.cover_oneLA B (by omega)
  · exact BB6.Agent6F0.cover_oneLE B (by omega)
  · exact BB6.Agent6F0.cover_zeroLB B
  · exact BB6.Agent6F0.cover_oneLC B
  · exact BB6.Agent6F0.Counter0LC.cover_zeroLC B
  · exact BB6.Agent6F0.Long.cover_oneRC B hB
  · exact BB6.Agent6F0.Counter0LE.cover_zeroLE B
  · exact BB6.Agent6F0.Counter1RD.cover_oneRD B
  · exact BB6.Agent6F0.AFirst.cover_oneLD B (by omega)
  · exact BB6.Agent6F0.RB.cover_oneRB B (by omega)

def closedF0 (p : PartialMachine) : Bool :=
  closedMoves.any fun f => sameTable p (BB6.Agent6F0.parent f)

theorem cover_closed (B : Nat) (hB : 49394 ≤ B) (p : PartialMachine)
    (hc : closedF0 p = true) : Cover (WeightedBound B) p := by
  rcases List.any_eq_true.mp hc with ⟨f,hf,he⟩
  rw [sameTable_sound he]
  exact cover_move B hB f hf

/-- Remove exactly the certified tables from the explicit raw139 residual
    roster. The filter consumes full tables, not ordinal labels. -/
noncomputable def remaining : List (List Move × PartialMachine) :=
  championResidualFrontierWithParentResiduals.filter fun e => !closedF0 e.2

theorem removed_count :
    (championResidualFrontierWithParentResiduals.filter fun e => closedF0 e.2).length = 10 := by decide

theorem remaining_count : remaining.length = 113 := by decide

theorem residual_cover
    (hLeaves : ∀ e ∈ remaining, Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual := by
  apply cover_of_championResidual_frontier
  intro e he
  cases hc : closedF0 e.2 with
  | true => exact cover_closed championScore champion_score_ge_49394 e.2 hc
  | false => exact hLeaves e (List.mem_filter.mpr ⟨he,by simp [hc]⟩)

theorem exact_from_remaining
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remaining, Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore := by
  apply exact_from_nonchampion_roster_covers_and_parent_frontier hOther
  intro e he
  cases hc : closedF0 e.2 with
  | true => exact cover_closed championScore champion_score_ge_49394 e.2 hc
  | false => exact hLeaves e (List.mem_filter.mpr ⟨he,by simp [hc]⟩)

#print axioms base_eq_championP6
#print axioms parent_eq_championChild
#print axioms champion_score_ge_49394
#print axioms cover_closed
#print axioms removed_count
#print axioms remaining_count
#print axioms residual_cover
#print axioms exact_from_remaining

end BB6.Agent6F0.Integration

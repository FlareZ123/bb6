import TM63M1EvenRootComposition
import M0OddQ4Prefix
import M2EvenQ4Prefix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Root-connected M1-even, M0-odd, M2-even counted itinerary

This module takes the authentic blank-root q4/drain endpoint through three
successive original-source counted increments: (m,n)=(1,6), (0,5), (2,4).
The remaining conditional itinerary is thereby shortened to the state
S1(3,3,1,...), immediately after the m=2,n=4 even reset/drain.
-/

namespace BB6Coverage.Agent42M0M2RootComposition

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24M0OddQ4Prefix
open BB6Coverage.Agent42M2EvenQ4
open BB6Coverage.Agent42M1EvenSuffix
open BB6Coverage.Agent42M1EvenRootComposition
open BB6Coverage.Agent42RootAttainable
open BB6ChampionArithmetic

private theorem tm63NextRight_eq (b : Nat) :
    nextRight b = 2^b-1 := by
  rfl

private theorem tm63NextExponent_zero_eq (a b : Nat) :
    nextExponent 0 a b = a+b+1 := by
  rfl

private theorem tm63NextExponent_two_eq (a b : Nat) :
    nextExponent 2 a b = a+b+2 := by
  rfl

/-- Split the first two stages without evaluating the enormous right
counter: all exponent growth remains symbolic through nextRight. -/
private theorem tm63SectionResult_split_first_two (a b : Nat) :
    (sectionResult 5 0 a b).cost =
      proposedIncrementCost 0 5 a b +
      proposedIncrementCost 2 4 (nextExponent 0 a b) (nextRight b) +
      (sectionResult 3 1
        (nextExponent 2 (nextExponent 0 a b) (nextRight b))
        (nextRight (nextRight b))).cost := by
  simp [sectionResult,nextMarker,nextExponent]
  omega

/-- Readable aliases for the successive S1 endpoints.  Proof statements
below keep the nextRight expressions symbolic rather than unfolding them. -/
def tm63AfterM0OddA : Nat :=
  nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB

def tm63AfterM0OddB : Nat :=
  nextRight tm63AfterM1EvenB

def tm63AfterM0OddHead : Int :=
  tm63AfterM1EvenHead + 5 + 3*tm63AfterM1EvenB

def tm63AfterM2EvenA : Nat :=
  nextExponent 2 tm63AfterM0OddA tm63AfterM0OddB

def tm63AfterM2EvenB : Nat :=
  nextRight tm63AfterM0OddB

def tm63AfterM2EvenHead : Int :=
  tm63AfterM0OddHead + 5 + 3*tm63AfterM0OddB

/-- Exact symbolic length of the blank-root prefix through the three
source-proved counted increments.  Parentheses preserve the root+M1 prefix
as the first compositional block. -/
def tm63AfterM2EvenMoves : Nat :=
  (rootQ4DrainMoves + proposedIncrementCost 1 6 71 (2^63-1)) +
    (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
      proposedIncrementCost 2 4
        (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
        (nextRight tm63AfterM1EvenB))

/-- Exact symbolic residual after the proved M0-odd and M2-even stages. -/
def tm63AfterM2EvenSteps : Nat :=
  (sectionResult 3 1
    (nextExponent 2
      (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
      (nextRight tm63AfterM1EvenB))
    (nextRight (nextRight tm63AfterM1EvenB))).cost +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
    tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

private theorem tm63_after_m0_positivity :
    0 < tm63AfterM1EvenA := by
  dsimp [tm63AfterM1EvenA]
  omega

private theorem tm63_after_m2_positivity :
    0 < nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB := by
  rw [tm63NextExponent_zero_eq]
  omega

/-- The m=0,n=5 prefix followed by the all-ones drain is exactly its
proposed counted increment, with the full tape retained. -/
theorem m0Odd_counted_increment_from_after_m1 :
    run tm2
      (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB)
      (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
        tm63AfterM1EvenHead) =
      some (s1Config 3 4 2
        (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB) 0
        (nextRight tm63AfterM1EvenB)
        (tm63AfterM1EvenHead+5+3*tm63AfterM1EvenB)) := by
  have hp := m0Odd_reset_prefix_to_s1
    tm63AfterM1EvenA tm63AfterM1EvenB tm63AfterM1EvenHead
    tm63_after_m0_positivity
  have hbound := resetDrainBound
    tm63AfterM1EvenA tm63AfterM1EvenB 0 tm63_after_m0_positivity
  have hrun := s1Config_reset_prefix_then_counted_drain
    3 4 2
    (tm63AfterM1EvenA+tm63AfterM1EvenB+1)
    tm63AfterM1EvenB
    (tm63AfterM1EvenHead+5+3*tm63AfterM1EvenB)
    (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
      tm63AfterM1EvenHead)
    (resetPrefixCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB)
    hp (by simpa [resetDelta] using hbound)
  simpa only [proposedIncrementCost_decomp,
    tm63NextExponent_zero_eq,tm63NextRight_eq] using hrun

/-- The two remaining source-proved increments after the M1-even endpoint
compose to the M1,n=3 state following the M2-even counted drain. -/
theorem m0_m2_counted_chain_from_after_m1 :
    run tm2
      (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
       proposedIncrementCost 2 4
        (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
        (nextRight tm63AfterM1EvenB))
      (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
        tm63AfterM1EvenHead) =
      some (s1Config 3 3 1
        (nextExponent 2
          (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
          (nextRight tm63AfterM1EvenB)) 0
        (nextRight (nextRight tm63AfterM1EvenB))
        (tm63AfterM1EvenHead+5+3*tm63AfterM1EvenB+
          5+3*(nextRight tm63AfterM1EvenB))) := by
  rw [run_add,m0Odd_counted_increment_from_after_m1]
  simp only [Option.bind_some]
  have hm2 := m2Even_q4_counted_increment_source
    (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
    (nextRight tm63AfterM1EvenB)
    (tm63AfterM1EvenHead+5+3*tm63AfterM1EvenB)
    tm63_after_m2_positivity
  simpa only [tm63NextExponent_two_eq,tm63NextRight_eq] using hm2

/-- Authentic blank-root run through the root q4/drain endpoint and the
three successive counted increments (1,6), (0,5), (2,4). -/
theorem tm63_blank_reaches_after_m2_even :
    run tm2 tm63AfterM2EvenMoves blank =
      some (s1Config 3 3 1
        (nextExponent 2
          (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
          (nextRight tm63AfterM1EvenB)) 0
        (nextRight (nextRight tm63AfterM1EvenB))
        (tm63AfterM1EvenHead+5+3*tm63AfterM1EvenB+
          5+3*(nextRight tm63AfterM1EvenB))) := by
  unfold tm63AfterM2EvenMoves
  rw [run_add,tm63_blank_reaches_after_m1_even]
  simp only [Option.bind_some]
  exact m0_m2_counted_chain_from_after_m1

/-- The first five-stage residual itinerary after M1-even splits at its
first two reset stages, leaving the exact residual after M2-even. -/
theorem tm63AfterM1EvenSteps_split_m0_m2 :
    tm63AfterM1EvenSteps =
      proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
      proposedIncrementCost 2 4
        (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
        (nextRight tm63AfterM1EvenB) +
      tm63AfterM2EvenSteps := by
  have hsection := tm63SectionResult_split_first_two
    tm63AfterM1EvenA tm63AfterM1EvenB
  unfold tm63AfterM1EvenSteps tm63AfterM2EvenSteps
  rw [hsection]
  omega

/-- Root-connected attained-score theorem after the three proved counted
increments. Only the remaining (3,1)-onward itinerary and final terminal
reset are still supplied as explicit hypotheses. -/
theorem tm63_attainable_after_m2_even_q4
    (h : Int)
    (hstage :
      run tm2 tm63AfterM2EvenSteps
        (s1Config 3 3 1
          (nextExponent 2
            (nextExponent 0 tm63AfterM1EvenA tm63AfterM1EvenB)
            (nextRight tm63AfterM1EvenB)) 0
          (nextRight (nextRight tm63AfterM1EvenB))
          (tm63AfterM1EvenHead+5+3*tm63AfterM1EvenB+
            5+3*(nextRight tm63AfterM1EvenB))) =
        some (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++
          binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 (h+5+3*tm63FinalB))) :
    Attainable proposedChampionScore := by
  have hstageAfterM1 :
      run tm2 tm63AfterM1EvenSteps
        (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
          tm63AfterM1EvenHead) =
        some (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h) := by
    rw [tm63AfterM1EvenSteps_split_m0_m2,run_add,
      m0_m2_counted_chain_from_after_m1]
    simp only [Option.bind_some]
    exact hstage
  exact tm63_attainable_after_m1_even_q4 h hstageAfterM1 hfinal

#print axioms m0Odd_counted_increment_from_after_m1
#print axioms m0_m2_counted_chain_from_after_m1
#print axioms tm63_blank_reaches_after_m2_even
#print axioms tm63AfterM1EvenSteps_split_m0_m2
#print axioms tm63_attainable_after_m2_even_q4

end BB6Coverage.Agent42M0M2RootComposition

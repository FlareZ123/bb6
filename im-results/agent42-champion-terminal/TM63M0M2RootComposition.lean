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

/-- State parameters after the root-connected m=1,n=6 increment. -/
def tm63AfterM0OddA : Nat :=
  tm63AfterM1EvenA + tm63AfterM1EvenB + 1

def tm63AfterM0OddB : Nat :=
  2^tm63AfterM1EvenB - 1

def tm63AfterM0OddHead : Int :=
  tm63AfterM1EvenHead + 5 + 3*tm63AfterM1EvenB

/-- State parameters after the root-connected m=0,n=5 increment. -/
def tm63AfterM2EvenA : Nat :=
  tm63AfterM0OddA + tm63AfterM0OddB + 2

def tm63AfterM2EvenB : Nat :=
  2^tm63AfterM0OddB - 1

def tm63AfterM2EvenHead : Int :=
  tm63AfterM0OddHead + 5 + 3*tm63AfterM0OddB

/-- Exact symbolic length of the blank-root prefix through the three
source-proved counted increments. -/
def tm63AfterM2EvenMoves : Nat :=
  rootQ4DrainMoves +
    (proposedIncrementCost 1 6 71 (2^63-1) +
      (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
        proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB))

/-- The first five-stage residual itinerary after M1-even splits at its
first two reset stages, leaving the exact residual after M2-even. -/
def tm63AfterM2EvenSteps : Nat :=
  (sectionResult 3 1 tm63AfterM2EvenA tm63AfterM2EvenB).cost +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
    tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

private theorem tm63_after_m0_positivity :
    0 < tm63AfterM1EvenA := by
  dsimp [tm63AfterM1EvenA]
  omega

private theorem tm63_after_m2_positivity :
    0 < tm63AfterM0OddA := by
  dsimp [tm63AfterM0OddA,tm63AfterM1EvenA,tm63AfterM1EvenB]
  omega

/-- The m=0,n=5 prefix followed by the all-ones drain is exactly its
proposed counted increment, with the full tape retained. -/
theorem m0Odd_counted_increment_from_after_m1 :
    run tm2
      (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB)
      (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
        tm63AfterM1EvenHead) =
      some (s1Config 3 4 2 tm63AfterM0OddA 0 tm63AfterM0OddB
        tm63AfterM0OddHead) := by
  have hp := m0Odd_reset_prefix_to_s1
    tm63AfterM1EvenA tm63AfterM1EvenB tm63AfterM1EvenHead
    tm63_after_m0_positivity
  have hbound := resetDrainBound
    tm63AfterM1EvenA tm63AfterM1EvenB 0 tm63_after_m0_positivity
  have hrun := s1Config_reset_prefix_then_counted_drain
    3 4 2 tm63AfterM0OddA tm63AfterM1EvenB tm63AfterM0OddHead
    (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
      tm63AfterM1EvenHead)
    (resetPrefixCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB)
    hp (by simpa [resetDelta] using hbound)
  simpa [proposedIncrementCost_decomp,tm63AfterM0OddA,
    tm63AfterM0OddB,tm63AfterM0OddHead] using hrun

/-- The two remaining source-proved increments after the M1-even endpoint
compose to the M1,n=3 state following the M2-even counted drain. -/
theorem m0_m2_counted_chain_from_after_m1 :
    run tm2
      (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
       proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB)
      (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
        tm63AfterM1EvenHead) =
      some (s1Config 3 3 1 tm63AfterM2EvenA 0 tm63AfterM2EvenB
        tm63AfterM2EvenHead) := by
  rw [run_add,m0Odd_counted_increment_from_after_m1]
  simp only [Option.bind_some]
  simpa [tm63AfterM2EvenA,tm63AfterM2EvenB,tm63AfterM2EvenHead] using
    m2Even_q4_counted_increment_source
      tm63AfterM0OddA tm63AfterM0OddB tm63AfterM0OddHead
      tm63_after_m2_positivity

/-- Authentic blank-root run through the root q4/drain endpoint and the
three successive counted increments (1,6), (0,5), (2,4). -/
theorem tm63_blank_reaches_after_m2_even :
    run tm2 tm63AfterM2EvenMoves blank =
      some (s1Config 3 3 1 tm63AfterM2EvenA 0 tm63AfterM2EvenB
        tm63AfterM2EvenHead) := by
  have hm1 := m1Even_q4_counted_increment_source
    71 (2^63-1) 223 (by decide)
  have hafterM1 :
      run tm2
        (proposedIncrementCost 1 6 71 (2^63-1) +
         (proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
          proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB))
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config 3 3 1 tm63AfterM2EvenA 0 tm63AfterM2EvenB
          tm63AfterM2EvenHead) := by
    rw [run_add,hm1]
    simp only [Option.bind_some]
    exact m0_m2_counted_chain_from_after_m1
  unfold tm63AfterM2EvenMoves
  rw [run_add,tm2_blank_reaches_q4_drain_endpoint]
  simp only [Option.bind_some]
  exact hafterM1

/-- The arithmetic residual after M1-even splits into the proved M0-odd
and M2-even increments plus the residual beginning at S1(3,3,1,...). -/
theorem tm63AfterM1EvenSteps_split_m0_m2 :
    tm63AfterM1EvenSteps =
      proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
      proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB +
      tm63AfterM2EvenSteps := by
  have h0 :
      (sectionResult 5 0 tm63AfterM1EvenA tm63AfterM1EvenB).cost =
        proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
          (sectionResult 4 2 tm63AfterM0OddA tm63AfterM0OddB).cost := by
    simp [sectionResult,nextMarker,nextExponent,nextRight,
      tm63AfterM0OddA,tm63AfterM0OddB]
  have h1 :
      (sectionResult 4 2 tm63AfterM0OddA tm63AfterM0OddB).cost =
        proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB +
          (sectionResult 3 1 tm63AfterM2EvenA tm63AfterM2EvenB).cost := by
    simp [sectionResult,nextMarker,nextExponent,nextRight,
      tm63AfterM2EvenA,tm63AfterM2EvenB]
  have hsection :
      (sectionResult 5 0 tm63AfterM1EvenA tm63AfterM1EvenB).cost =
        proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
          proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB +
          (sectionResult 3 1 tm63AfterM2EvenA tm63AfterM2EvenB).cost := by
    calc
      _ = proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
            (sectionResult 4 2 tm63AfterM0OddA tm63AfterM0OddB).cost := h0
      _ = proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
            (proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB +
              (sectionResult 3 1 tm63AfterM2EvenA tm63AfterM2EvenB).cost) := by
                rw [h1]
      _ = proposedIncrementCost 0 5 tm63AfterM1EvenA tm63AfterM1EvenB +
            proposedIncrementCost 2 4 tm63AfterM0OddA tm63AfterM0OddB +
              (sectionResult 3 1 tm63AfterM2EvenA tm63AfterM2EvenB).cost := by
                omega
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
        (s1Config 3 3 1 tm63AfterM2EvenA 0 tm63AfterM2EvenB
          tm63AfterM2EvenHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++
          binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 h)) :
    Attainable proposedChampionScore := by
  have hstageAfterM1 :
      run tm2 tm63AfterM1EvenSteps
        (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
          tm63AfterM1EvenHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) := by
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

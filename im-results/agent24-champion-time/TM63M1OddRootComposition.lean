import TM63M0M2RootComposition
import M1OddQ4Suffix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Root-connected m=1,n=3 odd reset extension

This module extends the existing blank-root chain (1,6), (0,5), (2,4)
by the newly derived (1,3) odd reset.  The source-level machine run is
proved conditionally on the upstream root endpoint modules; the remaining
itinerary now starts at S1(3,2,0,...).  Keep this in im-results until the
new prefix/suffix modules compile and pass the axiom audit.
-/

namespace BB6Coverage.Agent24M1OddRootComposition

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24M1OddSuffix
open BB6Coverage.Agent42M0M2RootComposition
open BB6Coverage.Agent42RootAttainable
open BB6ChampionArithmetic

/-- State parameters after the newly proved m=1,n=3 odd increment. -/
def tm63AfterM1OddA : Nat :=
  tm63AfterM2EvenA + tm63AfterM2EvenB + 2

def tm63AfterM1OddB : Nat :=
  2^tm63AfterM2EvenB - 1

def tm63AfterM1OddHead : Int :=
  tm63AfterM2EvenHead + 5 + 3*tm63AfterM2EvenB

/-- Exact symbolic blank-root prefix through four source-proved counted
increments: (1,6), (0,5), (2,4), and (1,3). -/
def tm63AfterM1OddMoves : Nat :=
  tm63AfterM2EvenMoves +
    proposedIncrementCost 1 3 tm63AfterM2EvenA tm63AfterM2EvenB

/-- Residual itinerary after the m=1,n=3 increment. -/
def tm63AfterM1OddSteps : Nat :=
  (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).cost +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
    tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

private theorem tm63_after_m1_odd_positivity :
    0 < tm63AfterM2EvenA := by
  dsimp [tm63AfterM2EvenA,tm63AfterM0OddA,tm63AfterM1EvenA,
    tm63AfterM1EvenB]
  omega

/-- The arithmetic residual after M2-even splits into the proved m=1,n=3
increment and the remaining itinerary beginning at S1(3,2,0,...). -/
theorem tm63AfterM2EvenSteps_split_m1_odd :
    tm63AfterM2EvenSteps =
      proposedIncrementCost 1 3 tm63AfterM2EvenA tm63AfterM2EvenB +
        tm63AfterM1OddSteps := by
  have hsection :
      (sectionResult 3 1 tm63AfterM2EvenA tm63AfterM2EvenB).cost =
        proposedIncrementCost 1 3 tm63AfterM2EvenA tm63AfterM2EvenB +
          (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).cost := by
    simp [sectionResult,nextMarker,nextExponent,nextRight,
      tm63AfterM1OddA,tm63AfterM1OddB]
  unfold tm63AfterM2EvenSteps tm63AfterM1OddSteps
  rw [hsection]
  omega

/-- Authentic blank-root source run through the four counted increments,
ending at the m=1,n=3 odd reset's canonical successor. -/
theorem tm63_blank_reaches_after_m1_odd :
    run tm2 tm63AfterM1OddMoves blank =
      some (s1Config 3 2 0 tm63AfterM1OddA 0 tm63AfterM1OddB
        tm63AfterM1OddHead) := by
  unfold tm63AfterM1OddMoves
  rw [run_add,tm63_blank_reaches_after_m2_even]
  simp only [Option.bind_some]
  simpa [tm63AfterM1OddA,tm63AfterM1OddB,tm63AfterM1OddHead] using
    m1Odd_q4_counted_increment_source
      tm63AfterM2EvenA tm63AfterM2EvenB tm63AfterM2EvenHead
      tm63_after_m1_odd_positivity

/-- The remaining champion itinerary may now be started directly from
S1(3,2,0,...), rather than from S1(3,3,1,...). -/
theorem tm63_attainable_after_m1_odd_q4
    (h : Int)
    (hstage :
      run tm63AfterM1OddSteps
        (s1Config 3 2 0 tm63AfterM1OddA 0 tm63AfterM1OddB
          tm63AfterM1OddHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++
          binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 h)) :
    Attainable proposedChampionScore := by
  have hstageAfterM2 :
      run tm63AfterM2EvenSteps
        (s1Config 3 3 1 tm63AfterM2EvenA 0 tm63AfterM2EvenB
          tm63AfterM2EvenHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) := by
    rw [tm63AfterM2EvenSteps_split_m1_odd,run_add]
    rw [m1Odd_q4_counted_increment_source
      tm63AfterM2EvenA tm63AfterM2EvenB tm63AfterM2EvenHead
      tm63_after_m1_odd_positivity]
    simp only [Option.bind_some]
    simpa [tm63AfterM1OddA,tm63AfterM1OddB,tm63AfterM1OddHead] using hstage
  exact tm63_attainable_after_m2_even_q4 h hstageAfterM2 hfinal

#print axioms tm63AfterM2EvenSteps_split_m1_odd
#print axioms tm63_blank_reaches_after_m1_odd
#print axioms tm63_attainable_after_m1_odd_q4

end BB6Coverage.Agent24M1OddRootComposition

import TM63M1OddRootComposition
import M0EvenQ4Suffix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Root-connected m=0,n=2 even reset extension

This module extends the blank-root chain through the (1,3) odd stage
with the newly derived (0,2) even stage.  The next residual section
begins at S1(3,1,2,...), ready for the (2,1) reset.
-/

namespace BB6Coverage.Agent24TM63M0EvenRootComposition

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24M0EvenSuffix
open BB6Coverage.Agent24M1OddRootComposition
open BB6Coverage.Agent42RootAttainable
open BB6ChampionArithmetic

private theorem tm63SectionResult_split_m0_even (a b : Nat) :
    (sectionResult 2 0 a b).cost =
      proposedIncrementCost 0 2 a b +
        (sectionResult 1 2 (nextExponent 0 a b) (nextRight b)).cost := by
  simp [sectionResult,nextMarker,nextExponent]
  omega

def tm63AfterM0EvenA : Nat :=
  nextExponent 0 tm63AfterM1OddA tm63AfterM1OddB

def tm63AfterM0EvenB : Nat :=
  nextRight tm63AfterM1OddB

def tm63AfterM0EvenHead : Int :=
  tm63AfterM1OddHead + 5 + 3*tm63AfterM1OddB

/-- Exact symbolic blank-root prefix through five source-proved
counted increments: (1,6), (0,5), (2,4), (1,3), and (0,2). -/
def tm63AfterM0EvenMoves : Nat :=
  tm63AfterM1OddMoves +
    proposedIncrementCost 0 2 tm63AfterM1OddA tm63AfterM1OddB

/-- Residual itinerary after the m=0,n=2 even increment. -/
def tm63AfterM0EvenSteps : Nat :=
  (sectionResult 1 2 tm63AfterM0EvenA tm63AfterM0EvenB).cost +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
    tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

private theorem tm63_after_m0_even_positivity :
    0 < tm63AfterM1OddA := by
  have hnext :
      nextExponent 1 tm63AfterM2EvenA tm63AfterM2EvenB =
        tm63AfterM2EvenA+tm63AfterM2EvenB+2 := by
    rfl
  rw [tm63AfterM1OddA,hnext]
  omega

/-- The arithmetic residual after M1-odd splits into the proved m=0,n=2
increment and the remaining itinerary beginning at S1(3,1,2,...). -/
theorem tm63AfterM1OddSteps_split_m0_even :
    tm63AfterM1OddSteps =
      proposedIncrementCost 0 2 tm63AfterM1OddA tm63AfterM1OddB +
        tm63AfterM0EvenSteps := by
  have hsection := tm63SectionResult_split_m0_even
    tm63AfterM1OddA tm63AfterM1OddB
  simp only [tm63AfterM1OddSteps,tm63AfterM0EvenSteps,
    tm63AfterM0EvenA,tm63AfterM0EvenB,
    tm63AfterM1OddA,tm63AfterM1OddB]
  rw [hsection]

/-- Authentic blank-root source run through the five counted increments,
ending at the m=0,n=2 even reset's canonical successor. -/
theorem tm63_blank_reaches_after_m0_even :
    run tm2 tm63AfterM0EvenMoves blank =
      some (s1Config 3 1 2 tm63AfterM0EvenA 0 tm63AfterM0EvenB
        tm63AfterM0EvenHead) := by
  unfold tm63AfterM0EvenMoves
  rw [run_add,tm63_blank_reaches_after_m1_odd]
  simp only [Option.bind_some]
  simpa only [tm63AfterM0EvenA,tm63AfterM0EvenB,tm63AfterM0EvenHead] using
    m0Even_q4_counted_increment_source_symbolic
      tm63AfterM1OddA tm63AfterM1OddB tm63AfterM1OddHead
      tm63_after_m0_even_positivity

/-- The remaining champion itinerary may now be started directly from
S1(3,1,2,...), rather than from S1(3,2,0,...). -/
theorem tm63_attainable_after_m0_even_q4
    (h : Int)
    (hstage :
      run tm63AfterM0EvenSteps
        (s1Config 3 1 2 tm63AfterM0EvenA 0 tm63AfterM0EvenB
          tm63AfterM0EvenHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++
          binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 h)) :
    Attainable proposedChampionScore := by
  have hstageAfterM1Odd :
      run tm63AfterM1OddSteps
        (s1Config 3 2 0 tm63AfterM1OddA 0 tm63AfterM1OddB
          tm63AfterM1OddHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) := by
    rw [tm63AfterM1OddSteps_split_m0_even,run_add]
    rw [m0Even_q4_counted_increment_source_symbolic
      tm63AfterM1OddA tm63AfterM1OddB tm63AfterM1OddHead
      tm63_after_m0_even_positivity]
    simp only [Option.bind_some]
    simpa only [tm63AfterM0EvenA,tm63AfterM0EvenB,tm63AfterM0EvenHead] using hstage
  exact tm63_attainable_after_m1_odd_q4 h hstageAfterM1Odd hfinal

#print axioms tm63AfterM1OddSteps_split_m0_even
#print axioms tm63_blank_reaches_after_m0_even
#print axioms tm63_attainable_after_m0_even_q4

end BB6Coverage.Agent24TM63M0EvenRootComposition

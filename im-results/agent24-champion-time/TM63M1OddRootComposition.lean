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
open BB6Coverage.Agent42M1EvenRootComposition
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootAttainable
open BB6ChampionArithmetic

/-- State parameters after the newly proved m=1,n=3 odd increment. -/
private theorem tm63NextExponent_one_eq (a b : Nat) :
    nextExponent 1 a b = a+b+2 := by
  rfl

private theorem tm63NextExponent_two_eq (a b : Nat) :
    nextExponent 2 a b = a+b+2 := by
  rfl

private theorem tm63NextRight_eq (b : Nat) :
    nextRight b = 2^b-1 := by
  rfl

private theorem tm63SectionResult_split_m1_odd (a b : Nat) :
    (sectionResult 3 1 a b).cost =
      proposedIncrementCost 1 3 a b +
        (sectionResult 2 0 (nextExponent 1 a b) (nextRight b)).cost := by
  simp [sectionResult,nextMarker,nextExponent]
  omega

def tm63AfterM1OddA : Nat :=
  nextExponent 1 tm63AfterM2EvenA tm63AfterM2EvenB

def tm63AfterM1OddB : Nat :=
  nextRight tm63AfterM2EvenB

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
  rw [tm63AfterM2EvenA,tm63NextExponent_two_eq]
  omega

/-- The arithmetic residual after M2-even splits into the proved m=1,n=3
increment and the remaining itinerary beginning at S1(3,2,0,...). -/
theorem tm63AfterM2EvenSteps_split_m1_odd :
    tm63AfterM2EvenSteps =
      proposedIncrementCost 1 3 tm63AfterM2EvenA tm63AfterM2EvenB +
        tm63AfterM1OddSteps := by
  have hsection := tm63SectionResult_split_m1_odd
    tm63AfterM2EvenA tm63AfterM2EvenB
  simp only [tm63AfterM2EvenSteps,tm63AfterM1OddSteps,
    tm63AfterM1OddA,tm63AfterM1OddB,
    tm63AfterM2EvenA,tm63AfterM2EvenB]
  rw [hsection]

/-- Authentic blank-root source run through the four counted increments,
ending at the m=1,n=3 odd reset's canonical successor. -/
theorem tm63_blank_reaches_after_m1_odd :
    run tm2 tm63AfterM1OddMoves blank =
      some (s1Config 3 2 0 tm63AfterM1OddA 0 tm63AfterM1OddB
        tm63AfterM1OddHead) := by
  unfold tm63AfterM1OddMoves
  rw [run_add,tm63_blank_reaches_after_m2_even]
  simp only [Option.bind_some]
  simpa only [tm63AfterM1OddA,tm63AfterM1OddB,tm63AfterM1OddHead] using
    m1Odd_q4_counted_increment_source_symbolic
      tm63AfterM2EvenA tm63AfterM2EvenB tm63AfterM2EvenHead
      tm63_after_m1_odd_positivity

/-- The cost of the source-connected blank-root prefix through M1-odd,
followed by the residual itinerary to the final reset input, is exactly the
published suffix cost. -/
theorem tm63AfterM1OddTotalSteps_eq_root_suffix :
    tm63AfterM1OddMoves + tm63AfterM1OddSteps =
      rootQ4DrainMoves + tm63SuffixSteps := by
  calc
    tm63AfterM1OddMoves + tm63AfterM1OddSteps =
        tm63AfterM2EvenMoves + tm63AfterM2EvenSteps := by
      rw [tm63AfterM1OddMoves, tm63AfterM2EvenSteps_split_m1_odd]
      omega
    _ = rootQ4DrainMoves + tm63SuffixSteps := by
      unfold tm63AfterM2EvenMoves
      rw [Nat.add_assoc, ← tm63AfterM1EvenSteps_split_m0_m2,
        Nat.add_assoc, ← tm63SuffixSteps_split_m1_even]

/-- The final (1,1) reset displaces the head by 5+3b.  With that
source-correct endpoint, the root-connected run through M1-odd composes
directly with the generic terminal adapter. -/
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
          (2^tm63FinalB-1) 0 (h+5+3*tm63FinalB))) :
    Attainable proposedChampionScore := by
  have hblank :
      run tm2 (tm63AfterM1OddMoves + tm63AfterM1OddSteps) blank =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) := by
    rw [run_add,tm63_blank_reaches_after_m1_odd]
    simp only [Option.bind_some]
    exact hstage
  have hatt := champion_attainable_after_s1_countedRst012_m1n1
    (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h)
    (tm63AfterM1OddMoves + tm63AfterM1OddSteps)
    tm63Length2 tm63FinalA tm63FinalB (h+5+3*tm63FinalB)
    tm63FinalA_pos hblank hfinal
  have hscore :
      tm63AfterM1OddMoves + tm63AfterM1OddSteps +
        proposedIncrementCost 1 1 tm63FinalA tm63FinalB +
        terminalMoves tm63Length2
          (tm63FinalA+tm63FinalB+resetDelta 1) + 7 =
        proposedChampionScore := by
    rw [tm63AfterM1OddTotalSteps_eq_root_suffix,
      ← tm63_root_score_decomposition]
  exact hscore ▸ hatt

#print axioms tm63AfterM2EvenSteps_split_m1_odd
#print axioms tm63_blank_reaches_after_m1_odd
#print axioms tm63AfterM1OddTotalSteps_eq_root_suffix
#print axioms tm63_attainable_after_m1_odd_q4

end BB6Coverage.Agent24M1OddRootComposition

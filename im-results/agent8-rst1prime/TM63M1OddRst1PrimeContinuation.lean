import TM63M1OddFirstSectionContinuation
import Rst1PrimeBridge6Source
import S1CountedDrain
import CostRecurrence
import Lean.Elab.Tactic.Omega

/-!
# Root-connected Rst1' reset continuation

This composes the source-verified Rst1' prefix macro with the uniform
S1 all-ones drain.  At the concrete first-section endpoint
S1(3,0,1,A,0,B), the macro plus drain is exactly resetCost 3 A B and
lands at the next middle-section input
S1(resetLength, resetIndex, 2, B, 0, 2^B-1).

The remaining middle/last itinerary is still an explicit source-run
obligation; this file does not claim the exact BB(6) score.
-/

namespace BB6Coverage.Agent8Rst1PrimeRoot

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent8Rst1PrimeTail
open BB6Coverage.Agent24M1OddRootComposition
open BB6Coverage.Agent4M1OddFirstSection
open BB6Coverage.Agent42RootAttainable
open BB6ChampionArithmetic

/-- The Rst1' source prefix and the parity-complete S1 drain together
have exactly the published resetCost. -/
theorem rst1Prime_resetCost_decomposition (L a b : Nat) :
    resetCost L a b =
      (97 + 12*(L+a) + 3*b) + drainCost (2^b-1) 0 := by
  unfold resetCost
  rw [← drainCost_binary_additive b]
  omega

/-- The new binary index after the Rst1' macro is precisely resetIndex. -/
theorem rst1Prime_resetIndex_three (a : Nat) :
    2^(3+a+2)-2^a-1 = resetIndex 3 a := by
  have hp : 2^(3+a+2) = 32*2^a := by
    rw [show 3+a+2 = 5+a by omega, Nat.pow_add]
    norm_num
  unfold resetIndex
  rw [hp]
  norm_num
  omega

/-- The absolute head after the first Rst1' reset and its counted drain. -/
def tm63AfterFirstResetHead : Int :=
  tm63AfterFirstSectionHead + 5 + 3*(tm63FirstSection.right : Int)

/-- The exact residual cost after the first Rst1' reset has been discharged. -/
def tm63AfterFirstResetSteps : Nat :=
  tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

/-- Root-prefix length through the first reset, including its counted drain. -/
def tm63AfterFirstResetMoves : Nat :=
  (tm63AfterM1OddMoves +
    (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).cost) +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right

/-- The Rst1' macro followed by the exact all-ones drain is the first
resetCost stage in the published TM63 itinerary. -/
theorem rst1Prime_first_reset_after_first_section :
    run tm2 (resetCost 3 tm63FirstSection.exponent tm63FirstSection.right)
      (s1Config 3 0 1 tm63FirstSection.exponent 0
        tm63FirstSection.right tm63AfterFirstSectionHead) =
      some (s1Config tm63Length1 tm63Index1 2
        tm63FirstSection.right 0 (nextRight tm63FirstSection.right)
        tm63AfterFirstResetHead) := by
  let a := tm63FirstSection.exponent
  let b := tm63FirstSection.right
  have hprefix := rst1Prime_counted_macro 3 a b tm63AfterFirstSectionHead
  have hbound : 2^b-1 < 2^b := by omega
  have hdrain := s1Config_reset_prefix_then_counted_drain
    (3+a+2) (2^(3+a+2)-2^a-1) 2 b b
    tm63AfterFirstResetHead
    (s1Config 3 0 1 a 0 b tm63AfterFirstSectionHead)
    (97+12*(3+a)+3*b)
    (by simpa [tm63AfterFirstResetHead] using hprefix)
    hbound
  have hcost := rst1Prime_resetCost_decomposition 3 a b
  have hlen : tm63Length1 = 3+a+2 := by
    simp [tm63Length1,a]
  have hidx : tm63Index1 = 2^(3+a+2)-2^a-1 := by
    simpa [tm63Index1,a] using (rst1Prime_resetIndex_three a).symm
  have hright : nextRight b = 2^b-1 := by rfl
  change run tm2 (resetCost 3 a b)
    (s1Config 3 0 1 a 0 b tm63AfterFirstSectionHead) =
      some (s1Config tm63Length1 tm63Index1 2 b 0
        (nextRight b) tm63AfterFirstResetHead)
  rw [hcost, hlen, hidx, hright]
  simpa [a,b,tm63AfterFirstResetHead] using hdrain

/-- The authentic blank-root run now reaches the state after the first
Rst1' reset and its complete counted drain. -/
theorem tm63_blank_reaches_after_first_reset :
    run tm2 tm63AfterFirstResetMoves blank =
      some (s1Config tm63Length1 tm63Index1 2
        tm63FirstSection.right 0 (nextRight tm63FirstSection.right)
        tm63AfterFirstResetHead) := by
  unfold tm63AfterFirstResetMoves
  rw [run_add, tm63_blank_reaches_after_first_section]
  simp only [Option.bind_some]
  exact rst1Prime_first_reset_after_first_section

/-- Splitting the first reset off leaves exactly the residual middle/last
itinerary defined above. -/
theorem tm63AfterFirstSectionSteps_split_first_reset :
    tm63AfterFirstSectionSteps =
      resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
        tm63AfterFirstResetSteps := by
  rfl

/-- Root attainment now needs only the source itinerary beginning after
the first Rst1' reset, rather than the entire continuation from the end of
the first seven-increment section. -/
theorem tm63_attainable_after_first_reset_q4
    (h : Int)
    (hstage :
      run tm2 tm63AfterFirstResetSteps
        (s1Config tm63Length1 tm63Index1 2
          tm63FirstSection.right 0 (nextRight tm63FirstSection.right)
          tm63AfterFirstResetHead) =
        some (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++
          binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 (h+5+3*tm63FinalB))) :
    Attainable proposedChampionScore := by
  have hstageFull :
      run tm2 tm63AfterFirstSectionSteps
        (s1Config 3 0 1 tm63FirstSection.exponent 0
          tm63FirstSection.right tm63AfterFirstSectionHead) =
        some (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h) := by
    rw [tm63AfterFirstSectionSteps_split_first_reset, run_add,
      rst1Prime_first_reset_after_first_section]
    simp only [Option.bind_some]
    exact hstage
  exact tm63_attainable_after_first_section_q4 h hstageFull hfinal

#print axioms rst1Prime_resetCost_decomposition
#print axioms rst1Prime_resetIndex_three
#print axioms rst1Prime_first_reset_after_first_section
#print axioms tm63_blank_reaches_after_first_reset
#print axioms tm63_attainable_after_first_reset_q4

end BB6Coverage.Agent8Rst1PrimeRoot

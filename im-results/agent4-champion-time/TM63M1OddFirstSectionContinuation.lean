import TM63M1OddRootComposition
import M0EvenQ4Suffix
import Q4RightEndpoint
import S1CountedDrain
import CostRecurrence
import Lean.Elab.Tactic.Omega

/-!
# Root continuation through the first seven-increment section

This module reuses Agent 6's odd-Rst2 q4 prefix, Agent 24's full q4
suffix endpoint, and Agent 24's M0-even (0,2) source theorem.  Its
contribution is the concrete (0,2)+(2,1) composition after M1-odd:
a blank-root run to the end of the first seven-increment section, and
a reduced remaining-itinerary hypothesis beginning at the first reset.

The counted-drain wrapper depends on the general source Inc0 theorem
through S1CountedDrain.  The full original-import CI workflow must compile
this module before its theorems are treated as verified.
-/

namespace BB6Coverage.Agent4M1OddFirstSection

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0EvenSuffix
open BB6Coverage.Agent24M1OddRoot
open BB6Coverage.Agent42M0M2RootComposition
open BB6ChampionArithmetic

/-- The generic odd-Rst2 q4 reset prefix has exactly the proposed
reset-prefix cost at (m,n)=(2,1). -/
private theorem m2Odd_resetPrefixCost_eq (a b : Nat) :
    resetPrefixCost 2 1 a b = 71+12*a+3*b := by
  have hv : v2 1 = 0 := v2_of_odd 1 (by decide)
  simp [resetPrefixCost,hv]

/-- The generic odd-Rst2 q4 source run, followed by the exact all-ones
binary-counter drain, is the complete proposed counted increment for
(m,n)=(2,1). -/
theorem m2Odd_q4_counted_increment_source
    (a b : Nat) (h : Int) (ha : 0<a) :
    run tm2 (proposedIncrementCost 2 1 a b)
      (s1Config 3 1 2 a 0 b h) =
      some (s1Config 3 0 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp0 := oddRst2_q4_counted_source 3 1 a b h (by decide) (by decide)
  have hp :
      run tm2 (resetPrefixCost 2 1 a b)
        (s1Config 3 1 2 a 0 b h) =
        some (s1Config 3 0 1 (a+b+2) (2^b-1) 0
          (h+5+3*b)) := by
    simpa [m2Odd_resetPrefixCost_eq] using hp0
  have hbound := resetDrainBound a b 2 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    3 0 1 (a+b+2) b (h+5+3*b)
    (s1Config 3 1 2 a 0 b h) (resetPrefixCost 2 1 a b)
    hp (by simpa [resetDelta] using hbound)
  simpa [proposedIncrementCost_decomp] using hrun

private theorem m2Odd_nextExponent (a b : Nat) :
    nextExponent 2 a b = a+b+2 := by
  rfl

private theorem m2Odd_nextRight (b : Nat) :
    nextRight b = 2^b-1 := by
  rfl

/-- Symbolic successor endpoint for the concrete (2,1) counted increment. -/
theorem m2Odd_q4_counted_increment_source_symbolic
    (a b : Nat) (h : Int) (ha : 0<a) :
    run tm2 (proposedIncrementCost 2 1 a b)
      (s1Config 3 1 2 a 0 b h) =
      some (s1Config 3 0 1 (nextExponent 2 a b) 0
        (nextRight b) (h+5+3*b)) := by
  simpa only [m2Odd_nextExponent,m2Odd_nextRight] using
    m2Odd_q4_counted_increment_source a b h ha

/-- Endpoint parameters of the two-stage sectionResult (2,0). -/
theorem sectionResult_2_0_endpoint (a b : Nat) :
    (sectionResult 2 0 a b).marker = 1 ∧
    (sectionResult 2 0 a b).exponent =
      nextExponent 2 (nextExponent 0 a b) (nextRight b) ∧
    (sectionResult 2 0 a b).right =
      nextRight (nextRight b) ∧
    (sectionResult 2 0 a b).cost =
      proposedIncrementCost 0 2 a b +
      proposedIncrementCost 2 1 (nextExponent 0 a b) (nextRight b) := by
  simp [sectionResult,nextMarker,nextExponent,nextRight]

/-- The (0,2)+(2,1) source chain from the state immediately after M1-odd.
The first step is Agent 24's M0-even q4 theorem; the second is the generic
odd-Rst2 q4 theorem plus the exact counted drain above. -/
theorem m0_m2_counted_chain_from_after_m1_odd
    (a b : Nat) (h : Int) (ha : 0<a) :
    run tm2
      (proposedIncrementCost 0 2 a b +
       proposedIncrementCost 2 1 (nextExponent 0 a b) (nextRight b))
      (s1Config 3 2 0 a 0 b h) =
      some (s1Config 3 0 1
        (nextExponent 2 (nextExponent 0 a b) (nextRight b)) 0
        (nextRight (nextRight b))
        (h+10+3*b+3*(nextRight b))) := by
  have ha1 : 0 < nextExponent 0 a b := by
    simp [nextExponent]
    omega
  have hm0 := m0Even_q4_counted_increment_source_symbolic a b h ha
  rw [run_add,hm0]
  simp only [Option.bind_some]
  have hm2 := m2Odd_q4_counted_increment_source_symbolic
    (nextExponent 0 a b) (nextRight b) (h+5+3*b) ha1
  simpa [nextExponent,nextRight,Nat.add_assoc,Nat.add_left_comm,
    Nat.add_comm] using hm2

/-- Exact source run for the sectionResult (2,0) residual. -/
theorem sectionResult_2_0_source
    (a b : Nat) (h : Int) (ha : 0<a) :
    run tm2 (sectionResult 2 0 a b).cost
      (s1Config 3 2 0 a 0 b h) =
      some (s1Config 3 0 (sectionResult 2 0 a b).marker
        (sectionResult 2 0 a b).exponent 0
        (sectionResult 2 0 a b).right
        (h+10+3*b+3*(nextRight b))) := by
  have hchain := m0_m2_counted_chain_from_after_m1_odd a b h ha
  have hfields := sectionResult_2_0_endpoint a b
  rw [hfields.2.2.2]
  simpa [hfields.1,hfields.2.1,hfields.2.2.1] using hchain

/-- Authentic blank-root run through the complete first seven-increment
section: the root prefix through M1-odd, then M0-even (0,2), then
odd-Rst2 (2,1). -/
theorem tm63_first_section_endpoint_params :
    (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).marker =
      tm63FirstSection.marker ∧
    (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).exponent =
      tm63FirstSection.exponent ∧
    (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).right =
      tm63FirstSection.right := by
  rfl


def tm63AfterFirstSectionHead : Int :=
  tm63AfterM1OddHead+10+3*tm63AfterM1OddB+
    3*(nextRight tm63AfterM1OddB)


theorem tm63_blank_reaches_after_first_section :
    run tm2
      (tm63AfterM1OddMoves +
        (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).cost)
      blank =
      some (s1Config 3 0 1 tm63FirstSection.exponent 0
        tm63FirstSection.right tm63AfterFirstSectionHead) := by
  have hparams := tm63_first_section_endpoint_params
  rw [run_add,tm63_blank_reaches_after_m1_odd]
  simp only [Option.bind_some]
  have hsource := sectionResult_2_0_source
    tm63AfterM1OddA tm63AfterM1OddB tm63AfterM1OddHead
    (by
      dsimp [tm63AfterM1OddA,nextExponent]
      omega)
  simpa [tm63AfterFirstSectionHead,hparams.1,hparams.2.1,hparams.2.2]
    using hsource

/-- The remaining first-reset/middle/last-pre itinerary after the first
seven-increment section. -/
def tm63AfterFirstSectionSteps : Nat :=
  resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
  tm63MiddleSection.cost +
  resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
  tm63LastPreSection.cost + 12*v2 tm63Index2

/-- The two symbolic increments after M1-odd are exactly the last two
increments of the original first section. -/
theorem tm63AfterM1OddSteps_split_first_section :
    tm63AfterM1OddSteps =
      (sectionResult 2 0 tm63AfterM1OddA tm63AfterM1OddB).cost +
        tm63AfterFirstSectionSteps := by
  rfl

/-- Root-connected attainment with the remaining obligation starting only
after the complete first seven-increment section. -/
theorem tm63_attainable_after_first_section_q4
    (h : Int)
    (hstage :
      run tm63AfterFirstSectionSteps
        (s1Config 3 0 1 tm63FirstSection.exponent 0
          tm63FirstSection.right tm63AfterFirstSectionHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++
          binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 (h+5+3*tm63FinalB))) :
    Attainable proposedChampionScore := by
  have hparams := tm63_first_section_endpoint_params
  have hstageAfterM1Odd :
      run tm63AfterM1OddSteps
        (s1Config 3 2 0 tm63AfterM1OddA 0 tm63AfterM1OddB
          tm63AfterM1OddHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) := by
    rw [tm63AfterM1OddSteps_split_first_section,run_add,
      sectionResult_2_0_source]
    simp only [Option.bind_some]
    simpa [tm63AfterFirstSectionHead,hparams.1,hparams.2.1,hparams.2.2]
      using hstage
  exact tm63_attainable_after_m1_odd_q4 h hstageAfterM1Odd hfinal

#print axioms m2Odd_q4_counted_increment_source
#print axioms m2Odd_q4_counted_increment_source_symbolic
#print axioms sectionResult_2_0_endpoint
#print axioms m0_m2_counted_chain_from_after_m1_odd
#print axioms sectionResult_2_0_source
#print axioms tm63_blank_reaches_after_first_section
#print axioms tm63_attainable_after_first_section_q4

end BB6Coverage.Agent4M1OddFirstSection

import TM63RootQ4Drain
import ChampionRootQ4Drain
import CostRecurrence
import S1ChampionCountedReset
import Lean.Elab.Tactic.Omega

/-!
# Root-connected TM63 attained-score interface

This is the single attained-score composition for the current blank-root
q4/drain prefix and the existing terminal counted-reset adapter.  The only
missing machine-specific input is the exact original-source continuation
from the q4/drain endpoint to the final m=1,n=1 reset input, together with
that final reset-prefix run.  No such continuation is asserted here.
-/

namespace BB6Coverage.Agent42RootAttainable

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent42TerminalJoin
open BB6ChampionArithmetic

/--
If the original TM63 table continues from the root-connected q4/drain
endpoint to the final S1 state with marker 1 and index 0, and the final
(1,1) reset prefix reaches the terminal S0 pre-drain state, then the
terminal adapter proves an attained Busy Beaver lower bound at the exact
composed primitive-step count.

The first premise is precisely the still-missing middle of the published
Coq itinerary; the second is the final Rst0/Rst1/Rst2 source prefix.  This
theorem does not assume that either premise has been proved.
-/
theorem tm2_attainable_after_root_q4_drain_to_terminal_reset
    (suffixSteps L a b : Nat) (h : Int)
    (ha : 0 < a)
    (hstage :
      run tm2 suffixSteps
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config L 0 1 a 0 b h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 a b)
        (s1Config L 0 1 a 0 b h) =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta 1) (2^b-1) 0 h)) :
    Attainable
      (rootQ4DrainMoves + suffixSteps +
        proposedIncrementCost 1 1 a b +
        terminalMoves L (a+b+resetDelta 1) + 7) := by
  have hblank :
      run tm2 (rootQ4DrainMoves + suffixSteps) blank =
        some (s1Config L 0 1 a 0 b h) := by
    rw [run_add tm2 blank rootQ4DrainMoves suffixSteps]
    rw [tm2_blank_reaches_q4_drain_endpoint]
    exact hstage
  exact champion_attainable_after_s1_countedRst012_m1n1
    (s1Config L 0 1 a 0 b h)
    (rootQ4DrainMoves + suffixSteps) L a b h ha hblank
    (by simpa [s1Config] using hfinal)

/--
Actual-champion form of the conditional attained-score theorem.  The six
extra root transitions are made explicit via Agent 24's run-level transport,
so the score is written as (champion primitive moves) + 1 for the final
undefined query, rather than hiding the offset in the generic adapter.
-/
theorem champion_attainable_after_root_q4_drain_to_terminal_reset
    (suffixSteps L a b : Nat) (h : Int)
    (ha : 0 < a)
    (hstage :
      run tm2 suffixSteps
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config L 0 1 a 0 b h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 a b)
        (s1Config L 0 1 a 0 b h) =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta 1) (2^b-1) 0 h)) :
    Attainable
      (championRootQ4DrainMoves + suffixSteps +
        proposedIncrementCost 1 1 a b +
        terminalMoves L (a+b+resetDelta 1) + 1) := by
  have htm2 := tm2_attainable_after_root_q4_drain_to_terminal_reset
    suffixSteps L a b h ha hstage hfinal
  have hscore :
      rootQ4DrainMoves + suffixSteps +
          proposedIncrementCost 1 1 a b +
          terminalMoves L (a+b+resetDelta 1) + 7 =
        championRootQ4DrainMoves + suffixSteps +
          proposedIncrementCost 1 1 a b +
          terminalMoves L (a+b+resetDelta 1) + 1 := by
    simp [championRootQ4DrainMoves]
    omega
  exact hscore ▸ htm2

/-- The blank-root q4/drain prefix is exactly the first proposed
Rst0/Rst1/Rst2 counted cost in the arithmetic itinerary, plus the initial
27,959-step source bridge. This identifies the concrete source prefix with
the first summand of `proposedTM63Moves`. -/
theorem rootQ4Drain_matches_first_reset_cost :
    rootQ4DrainMoves = 27959 + proposedIncrementCost 2 7 6 63 := by
  have hv : v2 7 = 0 := by decide
  have hp : 804 ≤ 6*4^63 + 42*2^63 := by decide
  simp [rootQ4DrainMoves, q4DrainMoves, proposedIncrementCost, hv] <;> omega

/-- The arithmetic Rsts1 recursion starts with precisely the q4/drain
stage: its first update is (n,m,a,b)=(7,2,6,63) to
(6,1,71,2^63-1). -/
theorem first_section_cost_decomposition :
    (sectionResult 7 2 6 63).cost =
      proposedIncrementCost 2 7 6 63 +
        (sectionResult 6 1 71 (2^63-1)).cost := by
  simp [sectionResult, nextMarker, nextExponent, nextRight]

/-- Exact arithmetic itinerary parameters, matching the three
`sectionResult` stages in `proposedTM63Moves`. -/
def tm63FirstSection : SectionResult := sectionResult 7 2 6 63

def tm63FirstRest : SectionResult := sectionResult 6 1 71 (2^63-1)

def tm63Length1 : Nat := 3 + tm63FirstSection.exponent + 2

def tm63Index1 : Nat := resetIndex 3 tm63FirstSection.exponent

def tm63MiddleSection : SectionResult :=
  sectionResult tm63Index1 2 tm63FirstSection.right (nextRight tm63FirstSection.right)

def tm63Length2 : Nat := tm63Length1 + tm63MiddleSection.exponent + 2

def tm63Index2 : Nat := resetIndex tm63Length1 tm63MiddleSection.exponent

def tm63LastSection : SectionResult :=
  sectionResult tm63Index2 2 tm63MiddleSection.right (nextRight tm63MiddleSection.right)

def tm63LastPreSection : SectionResult :=
  sectionResult (tm63Index2-1) 2 tm63MiddleSection.right (nextRight tm63MiddleSection.right)

def tm63FinalA : Nat := tm63LastPreSection.exponent

def tm63FinalB : Nat := tm63LastPreSection.right

/-- Remaining proposed primitive cost after the already source-connected
first q4/drain stage, but before the final (m,n)=(1,1) counted reset.  The
`12*v2 index2` correction is essential in Agent 24's snoc cost identity. -/
def tm63SuffixSteps : Nat :=
  tm63FirstRest.cost +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
    tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

/-- Positivity of the all-ones successor parameter. -/
theorem nextRight_pos (b : Nat) (hb : 0 < b) : 0 < nextRight b := by
  cases b with
  | zero => omega
  | succ b =>
      unfold nextRight
      have hp : 0 < 2^b := Nat.pow_pos (by decide)
      simp only [Nat.pow_succ]
      omega

theorem sectionResult_exponent_pos (n m a b : Nat) (ha : 0 < a) :
    0 < (sectionResult n m a b).exponent := by
  induction n generalizing m a b with
  | zero =>
      simpa [sectionResult] using ha
  | succ n ih =>
      simp only [sectionResult]
      have ha' : 0 < nextExponent m a b := by
        unfold nextExponent
        omega
      exact ih (nextMarker m) (nextExponent m a b) (nextRight b) ha'

theorem sectionResult_right_pos (n m a b : Nat) (hb : 0 < b) :
    0 < (sectionResult n m a b).right := by
  induction n generalizing m a b with
  | zero =>
      simpa [sectionResult] using hb
  | succ n ih =>
      simp only [sectionResult]
      exact ih (nextMarker m) (nextExponent m a b) (nextRight b)
        (nextRight_pos b hb)

/-- The actual second reset index is 2 mod 3, as established by the
symbolic parity argument in Agent 24's CostRecurrence. -/
theorem tm63_second_index_two : tm63Index2 % 3 = 2 := by
  simpa [tm63Index2, tm63Length1, tm63MiddleSection, tm63Index1, tm63FirstSection]
    using second_reset_index_two

/-- The configuration immediately before the final stage has
marker 1, matching the final reset adapter's source configuration. -/
theorem tm63_last_pre_marker_one : tm63LastPreSection.marker = 1 := by
  change (sectionResult (tm63Index2-1) 2 tm63MiddleSection.right
    (nextRight tm63MiddleSection.right)).marker = 1
  rw [sectionResult_marker]
  have hmod := tm63_second_index_two
  omega

/-- The final proposed reset starts at marker 1 and is exactly the
(m,n)=(1,1) reset consumed by the terminal adapter. -/
theorem tm63_last_stage_m1 :
    tm63LastSection.marker = 0 ∧
    tm63LastSection.exponent = tm63FinalA + tm63FinalB + 2 ∧
    tm63LastSection.right = 2^tm63FinalB - 1 ∧
    tm63LastSection.cost =
      tm63LastPreSection.cost + 12*v2 tm63Index2 +
        proposedIncrementCost 1 1 tm63FinalA tm63FinalB := by
  have h := sectionResult_last_stage_m1 tm63Index2
    tm63MiddleSection.right (nextRight tm63MiddleSection.right) tm63_second_index_two
  simpa [tm63LastSection, tm63LastPreSection, tm63FinalA, tm63FinalB] using h

theorem tm63FinalA_pos : 0 < tm63FinalA := by
  have hfirstRight : 0 < tm63FirstSection.right := by
    exact sectionResult_right_pos 7 2 6 63 (by decide)
  have hmiddleInputRight : 0 < nextRight tm63FirstSection.right := by
    exact nextRight_pos tm63FirstSection.right hfirstRight
  have hmiddleRight : 0 < tm63MiddleSection.right := by
    exact sectionResult_right_pos tm63Index1 2 tm63FirstSection.right
      (nextRight tm63FirstSection.right) hmiddleInputRight
  have hfinal := sectionResult_exponent_pos (tm63Index2-1) 2
    tm63MiddleSection.right (nextRight tm63MiddleSection.right) hmiddleRight
  simpa [tm63FinalA, tm63LastPreSection] using hfinal

/-- Exact arithmetic decomposition of the published candidate score into
the root/q4/drain prefix, the remaining itinerary, the final counted reset,
and the terminal tail.  This is an arithmetic identity only; the source-run
premises are supplied separately by the attained-score theorem below. -/
theorem tm63_root_score_decomposition :
    proposedChampionScore =
      rootQ4DrainMoves + tm63SuffixSteps +
        proposedIncrementCost 1 1 tm63FinalA tm63FinalB +
        terminalMoves tm63Length2 (tm63FinalA+tm63FinalB+resetDelta 1) + 7 := by
  rcases tm63_last_stage_m1 with ⟨hmarker, hexp, hright, hcost⟩
  unfold proposedChampionScore proposedTM63Moves
  dsimp [tm63FirstSection, tm63Length1, tm63Index1, tm63MiddleSection,
    tm63Length2, tm63Index2, tm63LastSection, tm63SuffixSteps,
    tm63FirstRest, tm63LastPreSection, tm63FinalA, tm63FinalB]
  rw [first_section_cost_decomposition]
  rw [hcost]
  rw [hexp]
  rw [rootQ4Drain_matches_first_reset_cost]
  simp [terminalCost, terminalMoves, resetDelta] <;> omega

/-- Same decomposition in the actual champion move convention: six root
relabeling moves are explicit, and the final undefined query contributes +1. -/
theorem tm63_champion_score_decomposition :
    proposedChampionScore =
      championRootQ4DrainMoves + tm63SuffixSteps +
        proposedIncrementCost 1 1 tm63FinalA tm63FinalB +
        terminalMoves tm63Length2 (tm63FinalA+tm63FinalB+resetDelta 1) + 1 := by
  have h := tm63_root_score_decomposition
  have hoffset :
      rootQ4DrainMoves + tm63SuffixSteps +
          proposedIncrementCost 1 1 tm63FinalA tm63FinalB +
          terminalMoves tm63Length2 (tm63FinalA+tm63FinalB+resetDelta 1) + 7 =
        championRootQ4DrainMoves + tm63SuffixSteps +
          proposedIncrementCost 1 1 tm63FinalA tm63FinalB +
          terminalMoves tm63Length2 (tm63FinalA+tm63FinalB+resetDelta 1) + 1 := by
    simp [championRootQ4DrainMoves]
    omega
  exact h.trans hoffset

/--
Fully specialized conditional theorem at the exact published candidate
score.  The only missing inputs are the original-table continuation from
the q4/drain endpoint through the remaining Coq itinerary to the final
m=1,n=1 reset input, and the final reset-prefix run itself.
-/
theorem tm63_attainable_at_proposedChampionScore
    (h : Int)
    (hstage :
      run tm2 tm63SuffixSteps
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++ binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 h)) :
    Attainable proposedChampionScore := by
  have hscore := champion_attainable_after_root_q4_drain_to_terminal_reset
    tm63SuffixSteps tm63Length2 tm63FinalA tm63FinalB h
    tm63FinalA_pos hstage hfinal
  exact tm63_champion_score_decomposition.symm ▸ hscore

#print axioms tm63_attainable_at_proposedChampionScore
#print axioms tm63_root_score_decomposition
#print axioms tm63_champion_score_decomposition

/-- The root component already has a closed exact cost, independent of the
unknown middle itinerary. -/
theorem rootQ4Drain_attained_prefix_length :
    rootQ4DrainMoves = 6*4^63 + 42*2^63 + 27487 :=
  rootQ4DrainMoves_closed

#print axioms tm2_attainable_after_root_q4_drain_to_terminal_reset
#print axioms rootQ4Drain_matches_first_reset_cost
#print axioms first_section_cost_decomposition
#print axioms rootQ4Drain_attained_prefix_length
#print axioms champion_attainable_after_root_q4_drain_to_terminal_reset

end BB6Coverage.Agent42RootAttainable

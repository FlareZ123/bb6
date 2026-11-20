import GeneralQ4TailS1Config
import S1CountedDrain
import TM63SourceIncrementDispatcherComplete
import TerminalEncoderBridge
import TerminalAfterPrefix
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary-A q4Tail frame to terminal SectionBits

This generalizes A2TerminalResetComposition from A=2 to all A>=2.
The complete source chain remains a draft pending local Lean compilation
and transitive axiom audit.
-/

namespace BB6Coverage.Agent44GeneralQ4TailTerminal

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent38RootQ4TailS0
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent44GeneralQ4TailArithmetic
open BB6Coverage.Agent44GeneralQ4TailReparam
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42TerminalJoin
open BB6Coverage.Agent44SectionResultRunSource
open BB6ChampionArithmetic

/-- The outer SectionResult width obtained from an arbitrary-A q4Tail. -/
def q4TerminalWidth (L A : Nat) : Nat := A+L+2

/-- The arbitrary-A outer index encoded by the q4Tail residual. -/
def q4TerminalIndex (L A : Nat) : Nat := firstQ4P1M L A-3

/-- The complete SectionResult endpoint for the generalized q4Tail. -/
def q4TerminalResult (L A z : Nat) : SectionResult :=
  sectionResult (q4TerminalIndex L A) 0
    (q4TerminalUnary z) (q4TerminalRight z)

/-- Head after all outer SectionResult decrements. -/
def q4TerminalFinalHead (L A z : Nat) : Int :=
  sectionHeadAfter (q4TerminalIndex L A)
    (q4TerminalRight z) (q4TerminalHead z)

/-- Exact cost from the q4Tail frame through counted drain and dispatcher. -/
def q4TerminalPrefixCost (L A z : Nat) : Nat :=
  drainCost (q4TerminalRight z) 0 + (q4TerminalResult L A z).cost

private theorem q4TerminalIndex_lt (L A : Nat) :
    q4TerminalIndex L A < 2^(q4TerminalWidth L A) := by
  have hp : 0 < 2^(L+2) := Nat.pow_pos (by decide)
  have hbase : 2^(L+2)-1 < 2^(L+2) := by omega
  have hmul :
      2^A*(2^(L+2)-1) < 2^A*2^(L+2) :=
    Nat.mul_lt_mul_of_pos_left hbase (Nat.pow_pos (by decide))
  have hpow : 2^A*2^(L+2)=2^(A+L+2) := by
    calc
      2^A*2^(L+2) = 2^(A+(L+2)) := by rw [← Nat.pow_add]
      _ = 2^(A+L+2) := by congr 1 <;> omega
  have hM : firstQ4P1M L A < 2^(A+L+2) := by
    unfold firstQ4P1M
    rw [hpow]
    exact hmul
  unfold q4TerminalIndex q4TerminalWidth
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hM

private theorem q4TerminalUnary_pos (z : Nat) :
    0<q4TerminalUnary z := by
  have hp : 0<2^z := Nat.pow_pos (by decide)
  have hK : 0<q4TerminalPrefixBlocks z := by
    unfold q4TerminalPrefixBlocks
    omega
  have hn : 1≤q4TerminalInnerCount z := by
    unfold q4TerminalInnerCount
    have hp : 0<2^(2^z-1) := Nat.pow_pos (by decide)
    omega
  unfold q4TerminalUnary
  omega

private theorem q4TerminalDrainBound (z : Nat) :
    q4TerminalRight z < 2^(q4TerminalUnary z) := by
  have hn : 1≤q4TerminalInnerCount z := by
    unfold q4TerminalInnerCount
    have hp : 0<2^(2^z-1) := Nat.pow_pos (by decide)
    omega
  have hpow :
      2^(q4TerminalInnerCount z-1) ≤
        2^(q4TerminalUnary z) := by
    apply Nat.pow_le_pow_right (by decide : 0<2)
    unfold q4TerminalUnary q4TerminalPrefixBlocks
    omega
  unfold q4TerminalRight
  omega

/-- The q4Tail adapter is exactly the arbitrary-A S1 configuration. -/
theorem q4TerminalFrame_eq_s1Config
    (L A z : Nat) (hA : 2≤A) (hz : 1≤z) :
    q4TailS0Frame z (A+L+1) (firstQ4P1Value L A) =
      s1Config (q4TerminalWidth L A) (q4TerminalIndex L A) 0
        (q4TerminalUnary z) (q4TerminalRight z) 0
        (q4TerminalHead z) := by
  simpa [q4TerminalWidth,q4TerminalIndex] using
    q4TailS0Frame_eq_generalS1Config L A z hA hz

/-- The S0 counted drain transfers the q4Tail's binary counter to the
right unary counter, leaving the exact complete-dispatcher input. -/
theorem q4TerminalFrame_counted_drain
    (L A z : Nat) (hA : 2≤A) (hz : 1≤z) :
    run tm2 (drainCost (q4TerminalRight z) 0)
      (q4TailS0Frame z (A+L+1) (firstQ4P1Value L A)) =
    some (s1Config (q4TerminalWidth L A) (q4TerminalIndex L A) 0
      (q4TerminalUnary z) 0 (q4TerminalRight z) (q4TerminalHead z)) := by
  rw [q4TerminalFrame_eq_s1Config L A z hA hz]
  exact s1Config_counted_drain
    (q4TerminalWidth L A) (q4TerminalIndex L A) 0
    (q4TerminalUnary z) (q4TerminalInnerCount z-1) 0
    (q4TerminalHead z) (q4TerminalDrainBound z)

/-- The complete dispatcher returns to marker zero when L is even. -/
theorem q4Terminal_final_marker_zero
    (L A z : Nat) (hL : 4≤L) (hA : 2≤A) (hLeven : L%2=0) :
    (q4TerminalResult L A z).marker = 0 := by
  unfold q4TerminalResult q4TerminalIndex
  rw [sectionResult_marker]
  have hN := q4TerminalIndex_mod_three L A hL hA hLeven
  omega

/-- Exact original-TM2 run from any A>=2 q4Tail frame to the terminal
marker-zero S1 configuration, provided L is even. -/
theorem q4TerminalFrame_to_terminalConfig
    (L A z : Nat) (hL : 4≤L) (hA : 2≤A)
    (hLeven : L%2=0) (hz : 1≤z) :
    run tm2 (q4TerminalPrefixCost L A z)
      (q4TailS0Frame z (A+L+1) (firstQ4P1Value L A)) =
    some (s1Config (q4TerminalWidth L A) 0 0
      (q4TerminalResult L A z).exponent 0
      (q4TerminalResult L A z).right
      (q4TerminalFinalHead L A z)) := by
  have hdrain := q4TerminalFrame_counted_drain L A z hA hz
  have hcount := sectionResult_run_complete
    (q4TerminalWidth L A) (q4TerminalIndex L A) 0
    (q4TerminalUnary z) (q4TerminalRight z) (q4TerminalHead z)
    (by unfold q4TerminalWidth; omega)
    (q4TerminalIndex_lt L A)
    (q4TerminalUnary_pos z)
  have hmarker := q4Terminal_final_marker_zero L A z hL hA hLeven
  unfold q4TerminalPrefixCost q4TerminalResult q4TerminalFinalHead
  rw [run_add,hdrain]
  simp only [Option.bind_some]
  rw [hmarker] at hcount
  exact hcount

/-- The terminal configuration has the SectionBits interface required by
the existing arbitrary-exterior terminal macro. -/
theorem q4TerminalFrame_terminalSection
    (L A z : Nat) :
    TerminalFinish.SectionBits (q4TerminalWidth L A)
      (q4TerminalResult L A z).exponent
      (s1Config (q4TerminalWidth L A) 0 0
        (q4TerminalResult L A z).exponent 0
        (q4TerminalResult L A z).right
        (q4TerminalFinalHead L A z)).tape
      (q4TerminalFinalHead L A z) := by
  simpa [s1Config] using
    (s0_reset_sectionBits (q4TerminalWidth L A)
      (q4TerminalResult L A z).exponent
      (q4TerminalResult L A z).right
      (q4TerminalFinalHead L A z))

/-- Conditional halting from any authentic blank-root prefix that reaches
the arbitrary-A q4Tail frame. -/
theorem q4TerminalFrame_blank_prefix_halts
    (L A z rootSteps : Nat) (hL : 4≤L) (hA : 2≤A)
    (hLeven : L%2=0) (hz : 1≤z)
    (hroot : run tm2 rootSteps blank =
      some (q4TailS0Frame z (A+L+1) (firstQ4P1Value L A))) :
    HaltsAfter tm2
      (rootSteps + q4TerminalPrefixCost L A z +
        terminalMoves (q4TerminalWidth L A)
          (q4TerminalResult L A z).exponent) := by
  have hpost := q4TerminalFrame_to_terminalConfig
    L A z hL hA hLeven hz
  have hprefix :
      run tm2 (rootSteps+q4TerminalPrefixCost L A z) blank =
        some (s1Config (q4TerminalWidth L A) 0 0
          (q4TerminalResult L A z).exponent 0
          (q4TerminalResult L A z).right
          (q4TerminalFinalHead L A z)) := by
    rw [run_add,hroot]
    simp only [Option.bind_some]
    exact hpost
  exact tm2_halts_after_terminal_prefix
    (rootSteps+q4TerminalPrefixCost L A z)
    (q4TerminalWidth L A) (q4TerminalResult L A z).exponent
    (s1Config (q4TerminalWidth L A) 0 0
      (q4TerminalResult L A z).exponent 0
      (q4TerminalResult L A z).right
      (q4TerminalFinalHead L A z)).tape
    (q4TerminalFinalHead L A z)
    (by simpa [s1Config,s0Config] using hprefix)
    (q4TerminalFrame_terminalSection L A z)

/-- The same conditional source composition gives an explicit BB(6)
attainable score, including the champion's seven-step terminal correction. -/
theorem q4TerminalFrame_blank_prefix_attainable
    (L A z rootSteps : Nat) (hL : 4≤L) (hA : 2≤A)
    (hLeven : L%2=0) (hz : 1≤z)
    (hroot : run tm2 rootSteps blank =
      some (q4TailS0Frame z (A+L+1) (firstQ4P1Value L A))) :
    Attainable
      (rootSteps + q4TerminalPrefixCost L A z +
        terminalMoves (q4TerminalWidth L A)
          (q4TerminalResult L A z).exponent + 7) := by
  have hpost := q4TerminalFrame_to_terminalConfig
    L A z hL hA hLeven hz
  have hprefix :
      run tm2 (rootSteps+q4TerminalPrefixCost L A z) blank =
        some (s1Config (q4TerminalWidth L A) 0 0
          (q4TerminalResult L A z).exponent 0
          (q4TerminalResult L A z).right
          (q4TerminalFinalHead L A z)) := by
    rw [run_add,hroot]
    simp only [Option.bind_some]
    exact hpost
  exact champion_attainable_after_terminal_prefix
    (rootSteps+q4TerminalPrefixCost L A z)
    (q4TerminalWidth L A) (q4TerminalResult L A z).exponent
    (s1Config (q4TerminalWidth L A) 0 0
      (q4TerminalResult L A z).exponent 0
      (q4TerminalResult L A z).right
      (q4TerminalFinalHead L A z)).tape
    (q4TerminalFinalHead L A z)
    (by simpa [s1Config,s0Config] using hprefix)
    (q4TerminalFrame_terminalSection L A z)

#print axioms q4TerminalFrame_eq_s1Config
#print axioms q4TerminalFrame_counted_drain
#print axioms q4TerminalFrame_to_terminalConfig
#print axioms q4TerminalFrame_blank_prefix_halts
#print axioms q4TerminalFrame_blank_prefix_attainable

end BB6Coverage.Agent44GeneralQ4TailTerminal

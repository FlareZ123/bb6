import GeneralQ4TailTerminalComposition
import TM63RootQ4Tail
import P2RootS0Identity
import TM63Length1Parity
import S1ResetBaseRun
import Lean.Elab.Tactic.Omega

/-!
# Authentic blank-root composition through the arbitrary-A q4Tail dispatcher

This is the intended full lower-bound composition. It remains a source draft
until the complete transitive Lean import closure is compiled and audited.
-/

namespace BB6Coverage.Agent44GeneralQ4TailRoot

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8RootShift
open BB6Coverage.Agent38RootQ4Tail
open BB6Coverage.Agent38RootQ4TailS0
open BB6Coverage.Agent44GeneralQ4TailTerminal
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent42OuterLCInc
open BB6Coverage.Agent44TM63RootMarker1Endpoint
open BB6Coverage.Agent48RootFirstQ4Checkpoint
open BB6Coverage.Agent48ResetBaseEmbedding
open BB6Coverage.Agent42TerminalJoin
open BB6ChampionArithmetic

/-- The exact authentic blank-root prefix to the q4Tail frame. -/
def tm63GeneralTerminalRootSteps : Nat :=
  rootToSecondQ4Cost + rootSecondQ4TailPrefixCost

/-- Exact total halting time of the generalized direct-dispatcher route. -/
def tm63GeneralTerminalRootHaltTime : Nat :=
  tm63GeneralTerminalRootSteps +
    q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z +
    terminalMoves (q4TerminalWidth tm63Length1 rootMarker1A)
      (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).exponent

/-- The arbitrary-A direct dispatcher proves the authentic TM63 blank-root
trajectory halts; no repeated outer-width q4Tail recurrence is required. -/
theorem tm63_general_root_halts :
    HaltsAfter tm2 tm63GeneralTerminalRootHaltTime := by
  have hExpOdd : tm63FirstSection.exponent%2=1 :=
    tm63FirstSection_exponent_odd
  have hL : 4≤tm63Length1 := by
    unfold tm63Length1
    omega
  have hLeven : tm63Length1%2=0 := tm63Length1_even
  have hA : 2≤rootMarker1A := by
    unfold rootMarker1A
    have hr := tm63Middle34Result_right_ge_two
    omega
  have hz : 1≤rootMarker1Z := by
    have hz3 := rootMarker1Z_ge_three
    omega

  let w : Nat := firstQ4P1Width tm63Length1 rootMarker1A
  let q : Nat := firstQ4P1Value tm63Length1 rootMarker1A
  let frame : Config := q4TailS0Frame rootMarker1Z w q
  let finalResult := q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z
  let finalWidth := q4TerminalWidth tm63Length1 rootMarker1A
  let finalHead := q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z
  let finalConfig : Config :=
    s1Config finalWidth 0 0 finalResult.exponent 0 finalResult.right finalHead
  let finalShiftedHead : Int := finalHead+rootMarker1Head
  let suffixCost :=
    q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z

  have hframe :
      rootSecondQ4TailFrame = frame := by
    simpa [frame,w,q] using tm63_root_second_q4Tail_eq_q4TailS0Frame

  have hroot :
      run tm2 tm63GeneralTerminalRootSteps blank =
        some (shiftConfig rootMarker1Head frame) := by
    simpa [tm63GeneralTerminalRootSteps,frame,w,q,hframe] using
      tm63_blank_reaches_second_q4_tail

  have hpost :=
    q4TerminalFrame_to_terminalConfig
      tm63Length1 rootMarker1A rootMarker1Z hL hA hLeven hz

  have hpostShift :
      run tm2 suffixCost (shiftConfig rootMarker1Head frame) =
        some (shiftConfig rootMarker1Head finalConfig) := by
    calc
      run tm2 suffixCost (shiftConfig rootMarker1Head frame) =
          (run tm2 suffixCost frame).map (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2 frame suffixCost
      _ = some (shiftConfig rootMarker1Head finalConfig) := by
            simpa [suffixCost,finalConfig,finalResult,finalWidth,finalHead] using hpost

  have hprefix :
      run tm2 (tm63GeneralTerminalRootSteps+suffixCost) blank =
        some (shiftConfig rootMarker1Head finalConfig) := by
    rw [run_add,hroot]
    simp only [Option.bind_some]
    exact hpostShift

  have hshiftDiff :
      finalShiftedHead-finalHead = rootMarker1Head := by
    dsimp [finalShiftedHead]
    omega

  have hshiftConfig :
      shiftConfig rootMarker1Head finalConfig =
        s1Config finalWidth 0 0 finalResult.exponent 0
          finalResult.right finalShiftedHead := by
    have h := s1Config_shift finalWidth 0 0 finalResult.exponent 0
      finalResult.right finalHead finalShiftedHead
    simpa [finalConfig,finalShiftedHead,hshiftDiff] using h

  have hsection :
      TerminalFinish.SectionBits finalWidth finalResult.exponent
        (s1Config finalWidth 0 0 finalResult.exponent 0
          finalResult.right finalShiftedHead).tape finalShiftedHead := by
    simpa [s1Config] using
      (s0_reset_sectionBits finalWidth finalResult.exponent
        finalResult.right finalShiftedHead)

  have hprefix' :
      run tm2 (tm63GeneralTerminalRootSteps+suffixCost) blank =
        some (s1Config finalWidth 0 0 finalResult.exponent 0
          finalResult.right finalShiftedHead) := by
    rw [hshiftConfig] at hprefix
    exact hprefix

  simpa [tm63GeneralTerminalRootHaltTime,tm63GeneralTerminalRootSteps,
    suffixCost,finalResult,finalWidth] using
    tm2_halts_after_terminal_prefix
      (tm63GeneralTerminalRootSteps+suffixCost)
      finalWidth finalResult.exponent
      (s1Config finalWidth 0 0 finalResult.exponent 0 finalResult.right finalShiftedHead).tape
      finalShiftedHead hprefix' hsection

/-- The same composition yields an explicit attainable BB(6) lower bound. -/
theorem tm63_general_root_attainable :
    Attainable (tm63GeneralTerminalRootHaltTime+7) := by
  have hExpOdd : tm63FirstSection.exponent%2=1 :=
    tm63FirstSection_exponent_odd
  have hL : 4≤tm63Length1 := by
    unfold tm63Length1
    omega
  have hLeven : tm63Length1%2=0 := tm63Length1_even
  have hA : 2≤rootMarker1A := by
    unfold rootMarker1A
    have hr := tm63Middle34Result_right_ge_two
    omega
  have hz : 1≤rootMarker1Z := by
    have hz3 := rootMarker1Z_ge_three
    omega

  let w : Nat := firstQ4P1Width tm63Length1 rootMarker1A
  let q : Nat := firstQ4P1Value tm63Length1 rootMarker1A
  let frame : Config := q4TailS0Frame rootMarker1Z w q
  let finalResult := q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z
  let finalWidth := q4TerminalWidth tm63Length1 rootMarker1A
  let finalHead := q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z
  let finalConfig : Config :=
    s1Config finalWidth 0 0 finalResult.exponent 0 finalResult.right finalHead
  let finalShiftedHead : Int := finalHead+rootMarker1Head
  let suffixCost :=
    q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z

  have hframe :
      rootSecondQ4TailFrame = frame := by
    simpa [frame,w,q] using tm63_root_second_q4Tail_eq_q4TailS0Frame
  have hroot :
      run tm2 tm63GeneralTerminalRootSteps blank =
        some (shiftConfig rootMarker1Head frame) := by
    simpa [tm63GeneralTerminalRootSteps,frame,w,q,hframe] using
      tm63_blank_reaches_second_q4_tail
  have hpost :=
    q4TerminalFrame_to_terminalConfig
      tm63Length1 rootMarker1A rootMarker1Z hL hA hLeven hz
  have hpostShift :
      run tm2 suffixCost (shiftConfig rootMarker1Head frame) =
        some (shiftConfig rootMarker1Head finalConfig) := by
    calc
      run tm2 suffixCost (shiftConfig rootMarker1Head frame) =
          (run tm2 suffixCost frame).map (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2 frame suffixCost
      _ = some (shiftConfig rootMarker1Head finalConfig) := by
            simpa [suffixCost,finalConfig,finalResult,finalWidth,finalHead] using hpost
  have hprefix :
      run tm2 (tm63GeneralTerminalRootSteps+suffixCost) blank =
        some (shiftConfig rootMarker1Head finalConfig) := by
    rw [run_add,hroot]
    simp only [Option.bind_some]
    exact hpostShift
  have hshiftDiff :
      finalShiftedHead-finalHead = rootMarker1Head := by
    dsimp [finalShiftedHead]
    omega
  have hshiftConfig :
      shiftConfig rootMarker1Head finalConfig =
        s1Config finalWidth 0 0 finalResult.exponent 0
          finalResult.right finalShiftedHead := by
    have h := s1Config_shift finalWidth 0 0 finalResult.exponent 0
      finalResult.right finalHead finalShiftedHead
    simpa [finalConfig,finalShiftedHead,hshiftDiff] using h
  have hsection :
      TerminalFinish.SectionBits finalWidth finalResult.exponent
        (s1Config finalWidth 0 0 finalResult.exponent 0
          finalResult.right finalShiftedHead).tape finalShiftedHead := by
    simpa [s1Config] using
      (s0_reset_sectionBits finalWidth finalResult.exponent
        finalResult.right finalShiftedHead)

  have hprefix' :
      run tm2 (tm63GeneralTerminalRootSteps+suffixCost) blank =
        some (s1Config finalWidth 0 0 finalResult.exponent 0
          finalResult.right finalShiftedHead) := by
    rw [hshiftConfig] at hprefix
    exact hprefix
  simpa [tm63GeneralTerminalRootHaltTime,tm63GeneralTerminalRootSteps,
    suffixCost,finalResult,finalWidth] using
    champion_attainable_after_terminal_prefix
      (tm63GeneralTerminalRootSteps+suffixCost)
      finalWidth finalResult.exponent
      (s1Config finalWidth 0 0 finalResult.exponent 0 finalResult.right finalShiftedHead).tape
      finalShiftedHead hprefix' hsection

#print axioms tm63_general_root_halts
#print axioms tm63_general_root_attainable

end BB6Coverage.Agent44GeneralQ4TailRoot

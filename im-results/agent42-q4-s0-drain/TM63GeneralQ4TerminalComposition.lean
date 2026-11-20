import TM63RootQ4Tail
import P2RootS0FrameIdentity
import GeneralQ4TailTerminalComposition
import TM63Length1Parity
import TM63RootResidueSix
import RootShift
import Lean.Elab.Tactic.Omega

/-!
# Compose the authentic TM63 blank-root q4Tail prefix with arbitrary-A
# dispatcher terminalization.

The general q4Tail terminal theorem handles every A >= 2 when L is even.
This file joins it to the already drafted authentic blank-root run through
the second q4Tail frame.  The resulting lower-bound theorem is a source
composition only: its full dependency closure has not been locally
compiled or axiom-audited.  No BB(6) exact value is claimed.
-/

namespace BB6Coverage.Agent42TM63GeneralQ4Terminal

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent38RootQ4Tail
open BB6Coverage.Agent38RootQ4TailS0
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent42OuterLCInc
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent44GeneralQ4TailTerminal
open BB6Coverage.Agent48RootFirstQ4Checkpoint
open BB6Coverage.Agent48RootSecondQ4Frame
open BB6Coverage.Agent42TerminalJoin

/-- Encoder width of the root's terminal SectionResult. -/
def tm63GeneralQ4TerminalWidth : Nat :=
  q4TerminalWidth tm63Length1 rootMarker1A

/-- Complete SectionResult at the root's arbitrary-A q4Tail terminal cut. -/
def tm63GeneralQ4TerminalResult :=
  q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z

/-- Absolute head after the complete dispatcher, in root coordinates. -/
def tm63GeneralQ4TerminalHead : Int :=
  q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z +
    rootMarker1Head

/-- Exact source-TM2 prefix length from blank through the terminal S1 cut. -/
def tm63GeneralQ4TerminalPrefixCost : Nat :=
  rootToSecondQ4Cost + rootSecondQ4TailPrefixCost +
    q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z

/-- The terminal S1 reset configuration is equivariant under a head shift.
This is the only tape-coordinate transport needed in the root composition. -/
private theorem shift_s1_reset
    (L a b : Nat) (h j : Int) :
    shiftConfig j (s1Config L 0 0 a 0 b h) =
      s1Config L 0 0 a 0 b (h+j) := by
  let l : List Bool := markerWord 0 ++ d0 ++ binDec L 0 ++ lh
  change shiftConfig j (s0Config l a 0 b h) =
    s0Config l a 0 b (h+j)
  calc
    shiftConfig j (s0Config l a 0 b h) =
        shiftConfig j (shiftConfig h (s0Config l a 0 b 0)) := by
          rw [← s0Config_shift l a 0 b h]
    _ = shiftConfig (j+h) (s0Config l a 0 b 0) := by
          rw [shift_shift]
    _ = s0Config l a 0 b (h+j) := by
          rw [← s0Config_shift l a 0 b (h+j)]
          congr 1
          omega

/-- The authentic blank-root run reaches the arbitrary-A terminal S1 cut.

The root-specific hypotheses are L=76 (hence even), A>=2, and z>=3.
The proof uses the existing root-to-second-q4Tail theorem, the exact
rootSecondQ4TailFrame=q4TailS0Frame identity, and the general dispatcher
terminal composition. -/
theorem tm63_blank_reaches_general_q4_terminal :
    run tm2 tm63GeneralQ4TerminalPrefixCost blank =
      some (s1Config tm63GeneralQ4TerminalWidth 0 0
        tm63GeneralQ4TerminalResult.exponent 0
        tm63GeneralQ4TerminalResult.right
        tm63GeneralQ4TerminalHead) := by
  have hL : 4 ≤ tm63Length1 := tm63_root_length_ge_four
  have hA : 2 ≤ rootMarker1A := by
    dsimp [rootMarker1A]
    omega
  have hLeven : tm63Length1 % 2 = 0 := tm63Length1_even
  have hz : 1 ≤ rootMarker1Z :=
    le_trans (by decide) rootMarker1Z_ge_three

  have hframe :
      rootSecondQ4TailFrame =
        q4TailS0Frame rootMarker1Z
          (rootMarker1A + tm63Length1 + 1)
          (firstQ4P1Value tm63Length1 rootMarker1A) := by
    simpa [firstQ4P1Width] using
      tm63_root_second_q4Tail_eq_q4TailS0Frame

  have htail := q4TerminalFrame_to_terminalConfig
    tm63Length1 rootMarker1A rootMarker1Z hL hA hLeven hz

  have htailShift :
      run tm2 (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
        (shiftConfig rootMarker1Head rootSecondQ4TailFrame) =
      some (shiftConfig rootMarker1Head
        (s1Config (q4TerminalWidth tm63Length1 rootMarker1A) 0 0
          (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).exponent
          0 (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).right
          (q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z))) := by
    calc
      run tm2 (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
          (shiftConfig rootMarker1Head rootSecondQ4TailFrame) =
        run tm2 (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
          (shiftConfig rootMarker1Head
            (q4TailS0Frame rootMarker1Z
              (rootMarker1A + tm63Length1 + 1)
              (firstQ4P1Value tm63Length1 rootMarker1A))) := by
              rw [hframe]
      _ = (run tm2 (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
            (q4TailS0Frame rootMarker1Z
              (rootMarker1A + tm63Length1 + 1)
              (firstQ4P1Value tm63Length1 rootMarker1A))).map
              (shiftConfig rootMarker1Head) := by
                exact shift_run rootMarker1Head tm2
                  (q4TailS0Frame rootMarker1Z
                    (rootMarker1A + tm63Length1 + 1)
                    (firstQ4P1Value tm63Length1 rootMarker1A))
                  (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
      _ = some (shiftConfig rootMarker1Head
            (s1Config (q4TerminalWidth tm63Length1 rootMarker1A) 0 0
              (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).exponent
              0 (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).right
              (q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z))) := by
                rw [htail]
                rfl

  have hcompose :
      run tm2
        ((rootToSecondQ4Cost + rootSecondQ4TailPrefixCost) +
          q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
        blank =
      some (s1Config (q4TerminalWidth tm63Length1 rootMarker1A) 0 0
        (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).exponent
        0 (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).right
        (q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z +
          rootMarker1Head)) := by
    calc
      run tm2
          ((rootToSecondQ4Cost + rootSecondQ4TailPrefixCost) +
            q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
          blank =
        (run tm2 (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost) blank).bind
          (run tm2 (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)) := by
            exact run_append tm2 blank
              (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost)
              (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
      _ = run tm2 (q4TerminalPrefixCost tm63Length1 rootMarker1A rootMarker1Z)
            (shiftConfig rootMarker1Head rootSecondQ4TailFrame) := by
              rw [tm63_blank_reaches_second_q4_tail]
              simp only [Option.bind_some]
      _ = some (shiftConfig rootMarker1Head
            (s1Config (q4TerminalWidth tm63Length1 rootMarker1A) 0 0
              (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).exponent
              0 (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).right
              (q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z))) :=
            htailShift
      _ = some (s1Config (q4TerminalWidth tm63Length1 rootMarker1A) 0 0
            (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).exponent
            0 (q4TerminalResult tm63Length1 rootMarker1A rootMarker1Z).right
            (q4TerminalFinalHead tm63Length1 rootMarker1A rootMarker1Z +
              rootMarker1Head)) := by
                rw [shift_s1_reset]

  simpa [tm63GeneralQ4TerminalPrefixCost, tm63GeneralQ4TerminalWidth,
    tm63GeneralQ4TerminalResult, tm63GeneralQ4TerminalHead] using hcompose

/-- The composed authentic root endpoint satisfies the original terminal
SectionBits contract, now at the translated physical head. -/
theorem tm63_general_q4_terminalSectionBits :
    TerminalFinish.SectionBits tm63GeneralQ4TerminalWidth
      tm63GeneralQ4TerminalResult.exponent
      (s1Config tm63GeneralQ4TerminalWidth 0 0
        tm63GeneralQ4TerminalResult.exponent 0
        tm63GeneralQ4TerminalResult.right
        tm63GeneralQ4TerminalHead).tape
      tm63GeneralQ4TerminalHead := by
  simpa [s1Config] using
    s0_reset_sectionBits tm63GeneralQ4TerminalWidth
      tm63GeneralQ4TerminalResult.exponent
      tm63GeneralQ4TerminalResult.right
      tm63GeneralQ4TerminalHead

/-- Conditional source-TM2 halt theorem for the authentic blank root. -/
theorem tm63_blank_halts :
    HaltsAfter tm2
      (tm63GeneralQ4TerminalPrefixCost +
        terminalMoves tm63GeneralQ4TerminalWidth
          tm63GeneralQ4TerminalResult.exponent) := by
  exact tm2_halts_after_terminal_prefix
    tm63GeneralQ4TerminalPrefixCost
    tm63GeneralQ4TerminalWidth
    tm63GeneralQ4TerminalResult.exponent
    (s1Config tm63GeneralQ4TerminalWidth 0 0
      tm63GeneralQ4TerminalResult.exponent 0
      tm63GeneralQ4TerminalResult.right
      tm63GeneralQ4TerminalHead).tape
    tm63GeneralQ4TerminalHead
    (by
      simpa [s1Config, s0Config] using tm63_blank_reaches_general_q4_terminal)
    tm63_general_q4_terminalSectionBits

/-- An exact attainable lower-bound expression for the six-state champion,
conditional only on the source modules in this dependency chain compiling. -/
theorem tm63_blank_attainable :
    Attainable
      (tm63GeneralQ4TerminalPrefixCost +
        terminalMoves tm63GeneralQ4TerminalWidth
          tm63GeneralQ4TerminalResult.exponent + 7) := by
  exact champion_attainable_after_terminal_prefix
    tm63GeneralQ4TerminalPrefixCost
    tm63GeneralQ4TerminalWidth
    tm63GeneralQ4TerminalResult.exponent
    (s1Config tm63GeneralQ4TerminalWidth 0 0
      tm63GeneralQ4TerminalResult.exponent 0
      tm63GeneralQ4TerminalResult.right
      tm63GeneralQ4TerminalHead).tape
    tm63GeneralQ4TerminalHead
    (by
      simpa [s1Config] using tm63_blank_reaches_general_q4_terminal)
    tm63_general_q4_terminalSectionBits

#print axioms tm63_blank_reaches_general_q4_terminal
#print axioms tm63_general_q4_terminalSectionBits
#print axioms tm63_blank_halts
#print axioms tm63_blank_attainable

end BB6Coverage.Agent42TM63GeneralQ4Terminal

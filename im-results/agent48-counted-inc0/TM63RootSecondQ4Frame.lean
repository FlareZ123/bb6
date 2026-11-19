import TM63RootFirstQ4Checkpoint
import FirstQ4P1FrameBridge
import RootShift
import Lean.Elab.Tactic.Omega

/-!
# Authentic blank-root continuation to the second q4 frame

This composes Agent 44's blank-root-to-marker-1-S0 endpoint with Agent 42's
first-q4/P1/second-frame source theorem.  Translation invariance transports
the second q4 frame to the authentic root head.  This remains an intermediate
source draft until its full dependency closure is compiled and axiom-audited.
-/

namespace BB6Coverage.Agent48RootSecondQ4Frame

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent24FirstQ4Checkpoint
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent42FirstQ4P1FrameBridge
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent44TM63RootMiddle34
open BB6Coverage.Agent44TM63RootMarker1Endpoint
open BB6Coverage.Agent48RootFirstQ4Checkpoint

/-- Exact continuation cost from the marker-1 S0 entry through the second
positive-z q4 frame (first checkpoint, P1 prefix, all-ones drain, Q(z)). -/
def rootSecondQ4Cost : Nat :=
  (((drainCost rootMarker1Z 0 +
    ((97+12*(tm63Length1+rootMarker1A)+3*rootMarker1Z) +
      (6*4^rootMarker1Z+42*2^rootMarker1Z-12*rootMarker1Z-48))) +
    (9*rootMarker1Z+10)) +
    ((3*2^rootMarker1Z+3*rootMarker1Z+58) +
      ((6*4^(2^rootMarker1Z-1)+42*2^(2^rootMarker1Z-1)-
        12*(2^rootMarker1Z-1)-48) +
        (9*2^rootMarker1Z+9*rootMarker1Z+16)))

/-- The second q4 finite frame, in coordinates relative to the marker-1 S0
entry. -/
def rootSecondQ4Frame : Config :=
  frameAt
    (sweptLeft (3*(2^rootMarker1Z-1)+3*rootMarker1Z+7)
      (firstCycleS0DrainOutput rootMarker1Z
        (List.replicate 4 true ++
          binDec (firstQ4P1Width tm63Length1 rootMarker1A)
            (firstQ4P1Value tm63Length1 rootMarker1A) ++ lh)).tape
      (3*2^rootMarker1Z+3*rootMarker1Z+7))
    3 firstCyclePostludeInside firstCyclePostludeEnd

/-- Total exact primitive-step count from blank to the second q4 frame. -/
def rootToSecondQ4Cost : Nat :=
  rootToMarker1S0Cost + rootSecondQ4Cost

/-- The authentic blank TM63 trajectory reaches the second q4 frame after
one complete positive-z q4/P1 cycle. -/
theorem tm63_blank_reaches_second_q4_frame :
    run tm2 rootToSecondQ4Cost blank =
      some (shiftConfig rootMarker1Head rootSecondQ4Frame) := by
  have hroot :
      run tm2 rootToMarker1S0Cost blank =
        some (s0Config (firstQ4Left0 tm63Length1)
          rootMarker1A rootMarker1Z 0 rootMarker1Head) := by
    simpa [rootToMarker1S0Cost, rootMarker1A, rootMarker1Z,
      rootMarker1Head, s0Config, firstQ4Left0_eq_marker1_d1pow] using
      tm63_blank_reaches_after_middle34_marker1_s0

  have hz' : 1 ≤ rootMarker1Z := by
    omega

  have hsecond :
      run tm2 rootSecondQ4Cost
        (s0Config (firstQ4Left0 tm63Length1)
          rootMarker1A rootMarker1Z 0 0) =
        some rootSecondQ4Frame := by
    simpa [rootSecondQ4Cost, rootSecondQ4Frame] using
      firstQ4P1Root_to_secondFrame tm63Length1
        rootMarker1A rootMarker1Z rootMarker1A_pos
        rootMarker1Z_lt_pow hz'

  have hsecondAtRootHead :
      run tm2 rootSecondQ4Cost
        (s0Config (firstQ4Left0 tm63Length1)
          rootMarker1A rootMarker1Z 0 rootMarker1Head) =
        some (shiftConfig rootMarker1Head rootSecondQ4Frame) := by
    calc
      run tm2 rootSecondQ4Cost
          (s0Config (firstQ4Left0 tm63Length1)
            rootMarker1A rootMarker1Z 0 rootMarker1Head) =
        run tm2 rootSecondQ4Cost
          (shiftConfig rootMarker1Head
            (s0Config (firstQ4Left0 tm63Length1)
              rootMarker1A rootMarker1Z 0 0) ) := by
                rw [s0Config_shift]
      _ =
        (run tm2 rootSecondQ4Cost
          (s0Config (firstQ4Left0 tm63Length1)
            rootMarker1A rootMarker1Z 0 0)).map
          (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2
              (s0Config (firstQ4Left0 tm63Length1)
                rootMarker1A rootMarker1Z 0 0)
              rootSecondQ4Cost
      _ = some (shiftConfig rootMarker1Head rootSecondQ4Frame) := by
            rw [hsecond]

  calc
    run tm2 rootToSecondQ4Cost blank =
        (run tm2 rootToMarker1S0Cost blank).bind
          (run tm2 rootSecondQ4Cost) := by
            unfold rootToSecondQ4Cost
            exact run_append tm2 blank
              rootToMarker1S0Cost rootSecondQ4Cost
    _ = some (shiftConfig rootMarker1Head rootSecondQ4Frame) := by
          rw [hroot]
          simp only [Option.bind_some]
          exact hsecondAtRootHead

#print axioms tm63_blank_reaches_second_q4_frame

end BB6Coverage.Agent48RootSecondQ4Frame

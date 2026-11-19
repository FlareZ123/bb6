import TM63RootMarker1Endpoint
import FirstQ4CheckpointPostlude
import RootShift
import Lean.Elab.Tactic.Omega

/-!
# Authentic blank-root continuation to the first positive-z q4 checkpoint

This composes Agent 44's blank-root-to-marker-1-S0 endpoint with Agent 42's
four-stage first-q4-checkpoint source run.  Translation invariance transports
the checkpoint macro from head 0 to the actual root head.  The result is a
source-level exact run to the q4 finite frame; the dependency closure remains
uncompiled and this file is an intermediate result.
-/

namespace BB6Coverage.Agent48RootFirstQ4Checkpoint

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24FirstQ4Checkpoint
open BB6Coverage.Agent42FirstQ4Checkpoint
open BB6Coverage.Agent44TM63RootMiddle34
open BB6Coverage.Agent44TM63RootMarker1Endpoint
open BB6Coverage.Agent48Q4S0Macros

/-- Width of the authentic marker-1 S0 endpoint after middle 34. -/
def rootMarker1A : Nat :=
  middle34Result.exponent + middle34Result.right + 2

/-- Positive left binary counter at the authentic marker-1 S0 endpoint. -/
def rootMarker1Z : Nat :=
  2^middle34Result.right - 1

/-- Absolute head of the authentic marker-1 S0 endpoint. -/
def rootMarker1Head : Int :=
  middle34Head + 3*(middle34Result.right:Int) + 5

/-- Exact cost to reach the canonical marker-1 S0 configuration. -/
def rootToMarker1S0Cost : Nat :=
  tm63MiddleFirst34Moves + middle34Result.cost +
    (12*middle34Result.exponent + 8 + 63 +
      3*middle34Result.right)

/-- Exact first-q4-checkpoint continuation cost after the root S0 entry. -/
def rootFirstQ4Cost : Nat :=
  (drainCost rootMarker1Z 0 +
    ((97+12*(tm63Length1+rootMarker1A)+3*rootMarker1Z) +
      (6*4^rootMarker1Z+42*2^rootMarker1Z-12*rootMarker1Z-48))) +
    (9*rootMarker1Z+10)

/-- The first q4 checkpoint frame in coordinates relative to the root S0 head. -/
def rootFirstQ4Frame : Config :=
  q4FrameAt
    (s0LeftSweep (3*rootMarker1Z+2)
      (s0Config (firstQ4Left2 tm63Length1 rootMarker1A)
        rootMarker1Z 0 (2^rootMarker1Z-1)
        (3*rootMarker1Z+5)).tape
      (3*rootMarker1Z+5))
    3 q4S0Final4Inside q4S0Final4End

/-- Total exact primitive-step count from blank to the first q4 checkpoint. -/
def rootToFirstQ4Cost : Nat :=
  rootToMarker1S0Cost + rootFirstQ4Cost

/-- The authentic root endpoint satisfies the positive-width precondition
of the first q4 checkpoint macro. -/
theorem rootMarker1A_pos : 0 < rootMarker1A := by
  simpa [rootMarker1A] using
    tm63_blank_reaches_after_middle34_marker1_s0_input_bounds.1

/-- The authentic root endpoint satisfies the first q4 macro's binary
counter capacity bound. -/
theorem rootMarker1Z_lt_pow : rootMarker1Z < 2^rootMarker1A := by
  simpa [rootMarker1A, rootMarker1Z] using
    tm63_blank_reaches_after_middle34_marker1_s0_input_bounds.2

/-- The authentic positive-z branch is genuinely entered: z is at least 3. -/
theorem rootMarker1Z_ge_three : 3 ≤ rootMarker1Z := by
  simpa [rootMarker1Z] using tm63Middle34Result_z_ge_three

private theorem config_ext {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      simp only at hs hh ht
      subst ds
      subst dh
      subst dt
      rfl

/-- S0's absolute-coordinate encoder is equivariant under translation. -/
theorem s0Config_shift
    (l : List Bool) (a z b : Nat) (h : Int) :
    s0Config l a z b h = shiftConfig h (s0Config l a z b 0) := by
  apply config_ext
  · simp [s0Config, shiftConfig]
  · simp [s0Config, shiftConfig]
  · funext x
    by_cases hx : x ≤ h
    · have hle : x-h ≤ 0 := by omega
      have hdiff : h-x = 0-(x-h) := by omega
      simp [s0Config, s0Tape, shiftConfig, hx, hle, hdiff]
    · have hgt : ¬ x-h ≤ 0 := by omega
      simp [s0Config, s0Tape, shiftConfig, hx, hgt]

/-- The authentic blank TM63 trajectory reaches the first q4 checkpoint
of the positive-z S0 macro.  The endpoint is the exact q4 finite frame,
translated to the root's absolute head coordinate. -/
theorem tm63_blank_reaches_first_q4_checkpoint :
    run tm2 rootToFirstQ4Cost blank =
      some (shiftConfig rootMarker1Head rootFirstQ4Frame) := by
  have hroot :
      run tm2 rootToMarker1S0Cost blank =
        some (s0Config (firstQ4Left0 tm63Length1)
          rootMarker1A rootMarker1Z 0 rootMarker1Head) := by
    simpa [rootToMarker1S0Cost, rootMarker1A, rootMarker1Z,
      rootMarker1Head, s0Config, firstQ4Left0_eq_marker1_d1pow] using
      tm63_blank_reaches_after_middle34_marker1_s0

  have hz : rootMarker1Z < 2^rootMarker1A :=
    rootMarker1Z_lt_pow

  have hfirst :
      run tm2 rootFirstQ4Cost
        (s0Config (firstQ4Left0 tm63Length1)
          rootMarker1A rootMarker1Z 0 0) =
        some rootFirstQ4Frame := by
    simpa [rootFirstQ4Cost, rootFirstQ4Frame] using
      firstQ4Checkpoint_run tm63Length1 rootMarker1A rootMarker1Z hz

  have hfirstAtRootHead :
      run tm2 rootFirstQ4Cost
        (s0Config (firstQ4Left0 tm63Length1)
          rootMarker1A rootMarker1Z 0 rootMarker1Head) =
        some (shiftConfig rootMarker1Head rootFirstQ4Frame) := by
    calc
      run tm2 rootFirstQ4Cost
          (s0Config (firstQ4Left0 tm63Length1)
            rootMarker1A rootMarker1Z 0 rootMarker1Head) =
        run tm2 rootFirstQ4Cost
          (shiftConfig rootMarker1Head
            (s0Config (firstQ4Left0 tm63Length1)
              rootMarker1A rootMarker1Z 0 0)) := by
                rw [s0Config_shift]
      _ =
        (run tm2 rootFirstQ4Cost
          (s0Config (firstQ4Left0 tm63Length1)
            rootMarker1A rootMarker1Z 0 0)).map
          (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2
              (s0Config (firstQ4Left0 tm63Length1)
                rootMarker1A rootMarker1Z 0 0)
              rootFirstQ4Cost
      _ = some (shiftConfig rootMarker1Head rootFirstQ4Frame) := by
            rw [hfirst]

  calc
    run tm2 rootToFirstQ4Cost blank =
        (run tm2 rootToMarker1S0Cost blank).bind
          (run tm2 rootFirstQ4Cost) := by
            unfold rootToFirstQ4Cost
            exact run_append tm2 blank
              rootToMarker1S0Cost rootFirstQ4Cost
    _ = some (shiftConfig rootMarker1Head rootFirstQ4Frame) := by
          rw [hroot]
          simp only [Option.bind_some]
          exact hfirstAtRootHead

#print axioms tm63_blank_reaches_first_q4_checkpoint

end BB6Coverage.Agent48RootFirstQ4Checkpoint

import FirstQ4P1FrameRight
import FirstQ4P1Reparam
import Lean.Elab.Tactic.Omega

/-!
# Actual root q4 output = P1 checkpoint, then the complete first-cycle run

The left and right pointwise cell theorems identify the actual q4FrameAt
output with the side-based P1 tape. This file then composes the original
root-to-q4 run with Agent 48's already-proved P1 -> S0 drain -> Q(z) macro.
-/

namespace BB6Coverage.Agent42FirstQ4P1FrameBridge

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24FirstQ4Checkpoint
open BB6Coverage.Agent42FirstQ4Checkpoint
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent42FirstQ4P1FrameLeft
open BB6Coverage.Agent42FirstQ4P1FrameRight
open BB6Coverage.Agent42FirstQ4P1Reparam
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent48PositiveZSecondCycle
open BB6Coverage.Agent48PositiveZSetup
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent6Q4Prefix

private theorem config_ext {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp_all

/-- The actual final q4 frame configuration has state 4, head 1, and
exactly the canonical P1 side tape. -/
theorem firstQ4P1Output_eq_firstQ4P1Tape
    (L A z : Nat) (hA : 0<A) :
    firstQ4P1Output L A z = ⟨4,1,firstQ4P1Tape L A z⟩ := by
  have hs : (firstQ4P1Output L A z).state = 4 := by
    simp [firstQ4P1Output,q4FrameAt,q4Frame,shiftConfig,
      q4CenterTape,embed,q4S0Final4End]
  have hh : (firstQ4P1Output L A z).head = 1 := by
    simp [firstQ4P1Output,q4FrameAt,q4Frame,shiftConfig,
      q4CenterTape,embed,q4S0Final4End]
  have ht : (firstQ4P1Output L A z).tape = firstQ4P1Tape L A z := by
    funext x
    by_cases hx : x≤1
    · let i : Nat := Int.toNat (1-x)
      have hcoord : 1-(i:Int)=x := by
        have hcast : (i:Int)=1-x := by
          dsimp [i]
          exact Int.toNat_of_nonneg (by omega)
        omega
      have hleft := firstQ4P1Output_left_cell L A z i
      rw [hcoord] at hleft
      have htarget :
          firstQ4P1Tape L A z x =
            sideBit (firstQ4P1Left L A) i := by
        simp [firstQ4P1Tape,q4TapeFromSides,hx,i]
      exact hleft.trans htarget.symm
    · let i : Nat := Int.toNat (x-2)
      have hcoord : 2+(i:Int)=x := by
        have hcast : (i:Int)=x-2 := by
          dsimp [i]
          exact Int.toNat_of_nonneg (by omega)
        omega
      have hright := firstQ4P1Output_right_cell L A z i
      rw [hcoord] at hright
      have htarget :
          firstQ4P1Tape L A z x =
            sideBit (firstQ4P1Right z) i := by
        simp [firstQ4P1Tape,q4TapeFromSides,hx,i]
      exact hright.trans htarget.symm
  exact config_ext hs hh ht

/-- The genuine original-TM run from the marker-1 S0 root to the first
q4 checkpoint is exactly the canonical P1 checkpoint configuration. -/
theorem firstQ4Checkpoint_run_to_P1
    (L A z : Nat) (hA : 0<A) (hz : z<2^A) :
    run tm2
      ((drainCost z 0 +
        ((97+12*(L+A)+3*z) +
          (6*4^z+42*2^z-12*z-48))) +
        (9*z+10))
      (s0Config (firstQ4Left0 L) A z 0 0) =
    some ⟨4,1,firstCycleCheckpointTape z
      (firstQ4P1Width L A) (firstQ4P1Value L A)⟩ := by
  have hrun := firstQ4Checkpoint_run L A z hz
  have hframe :
      q4FrameAt
        (s0LeftSweep (3*z+2)
          (firstQ4P1SecondDrainTape L A z) (3*z+5))
        3 q4S0Final4Inside q4S0Final4End =
      firstQ4P1Output L A z := rfl
  rw [hframe,firstQ4P1Output_eq_firstQ4P1Tape L A z hA,
    firstQ4P1Tape_eq_firstCycleCheckpointTape L A z hA] at hrun
  exact hrun

private theorem run_append_some {n m : Nat} {c d e : Config}
    (h₁ : run tm2 n c = some d)
    (h₂ : run tm2 m d = some e) :
    run tm2 (n+m) c = some e := by
  simpa [run_append,h₁] using h₂

/-- Complete actual source run from the marker-1 S0 root, through its
first q4 checkpoint, the P1 prefix, the all-ones S0 drain, and Q(z), to
the second q4 frame. The first q4 output is no longer an assumed
side-based configuration: it is identified cell-by-cell above. -/
theorem firstQ4P1Root_to_secondFrame
    (L A z : Nat) (hA : 0<A) (hz : z<2^A) (hz' : 1≤z) :
    run tm2
      (((drainCost z 0 +
        ((97+12*(L+A)+3*z) +
          (6*4^z+42*2^z-12*z-48))) +
        (9*z+10)) +
        ((3*2^z+3*z+58) +
          ((6*4^(2^z-1)+42*2^(2^z-1)-12*(2^z-1)-48) +
            (9*2^z+9*z+16))))
      (s0Config (firstQ4Left0 L) A z 0 0) =
    some (frameAt
      (sweptLeft (3*(2^z-1)+3*z+7)
        (firstCycleS0DrainOutput z
          (List.replicate 4 true ++
            binDec (firstQ4P1Width L A) (firstQ4P1Value L A) ++ lh)).tape
        (3*2^z+3*z+7))
      3 firstCyclePostludeInside firstCyclePostludeEnd) := by
  have hfirst := firstQ4Checkpoint_run_to_P1 L A z hA hz
  have hsecond := positiveZFirstCycle_from_checkpoint z
    (firstQ4P1Width L A) (firstQ4P1Value L A)
    hz' (firstQ4P1Value_lt L A hA)
  exact run_append_some hfirst hsecond

#print axioms firstQ4P1Output_eq_firstQ4P1Tape
#print axioms firstQ4Checkpoint_run_to_P1
#print axioms firstQ4P1Root_to_secondFrame

end BB6Coverage.Agent42FirstQ4P1FrameBridge

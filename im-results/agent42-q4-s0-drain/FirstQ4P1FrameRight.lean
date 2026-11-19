import FirstQ4P1FrameLeft
import Lean.Elab.Tactic.Omega

/-!
# Right-facing cell proof for the first q4 frame -> P1 tape bridge

The output right stream is the three-cell q4 frame, followed by the
3z+2 cells written by the left sweep, followed by the source right stream
with its first (overwritten) cell removed. This is exactly the P1 right
side, up to its explicit four zero padding cells.
-/

namespace BB6Coverage.Agent42FirstQ4P1FrameRight

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24FirstQ4Checkpoint
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent42FirstQ4P1FrameLeft
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent6Q4Prefix

/-- Right-facing stream produced by the final q4 frame and the left scan,
before the canonical four-cell zero padding. -/
def firstQ4P1OutputRightSide (z : Nat) : List Bool :=
  [false,false,false] ++
    (List.replicate (3*z+2) true ++
      List.drop 1 (s0RightFacing (2^z-1)))

private theorem replicate_plus_three (n : Nat) :
    List.replicate (n+3) true =
      List.replicate n true ++ [true,true,true] := by
  rw [show n+3 = (n+2)+1 by omega, List.replicate_succ']
  rw [show n+2 = (n+1)+1 by omega, List.replicate_succ']
  rw [show n+1 = n+1 by rfl, List.replicate_succ']
  simp [List.append_assoc]

/-- The source right word, after the first cell is overwritten by the
sweep, is exactly the residual word in the canonical P1 encoding. -/
theorem firstQ4P1OutputRightSide_eq_target_appendZeros (z : Nat) :
    firstQ4P1OutputRightSide z ++ [false,false,false,false] =
      firstQ4P1Right z := by
  have hpow : 2^z-1+1 = 2^z := by
    have hp : 0 < 2^z := Nat.pow_pos (by decide)
    omega
  unfold firstQ4P1OutputRightSide firstQ4P1Right s0RightFacing
  rw [hpow]
  simp [List.drop, List.append_assoc]
  rw [replicate_plus_three (3*z+2)]
  simp [List.append_assoc]

private theorem sideBit_append_four_zeros (xs : List Bool) (i : Nat) :
    sideBit (xs ++ [false,false,false,false]) i = sideBit xs i := by
  by_cases hi : i < xs.length
  · exact sideBit_append_left xs [false,false,false,false] i hi
  · have hle : xs.length ≤ i := by omega
    rw [sideBit_append_right xs [false,false,false,false] i hle]
    rw [sideBit_ge_length xs i hle]
    by_cases hsmall : i-xs.length < 4
    · have hc : i-xs.length=0 ∨ i-xs.length=1 ∨
          i-xs.length=2 ∨ i-xs.length=3 := by omega
      rcases hc with h | h | h | h
      · rw [h]; simp [sideBit]
      · rw [h]; simp [sideBit]
      · rw [h]; simp [sideBit]
      · rw [h]; simp [sideBit]
    · exact sideBit_ge_length [false,false,false,false]
        (i-xs.length) (by simp; omega)

private theorem sideBit_drop_one (xs : List Bool) (i : Nat) :
    sideBit (List.drop 1 xs) i = sideBit xs (i+1) := by
  cases xs with
  | nil => simp [sideBit]
  | cons x xs => simp [List.drop,sideBit]

private theorem firstQ4P1OutputRightSide_eq_target_sideBit
    (z i : Nat) :
    sideBit (firstQ4P1Right z) i =
      sideBit (firstQ4P1OutputRightSide z) i := by
  rw [← firstQ4P1OutputRightSide_eq_target_appendZeros z]
  exact sideBit_append_four_zeros (firstQ4P1OutputRightSide z) i

private theorem sideBit_replicate_true (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      rw [List.replicate_succ]
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

private theorem firstQ4P1OutputRightSide_ones
    (z i : Nat) (hi : 3≤i) (hi' : i≤3*z+4) :
    sideBit (firstQ4P1OutputRightSide z) i = true := by
  have hidx : i-3 < 3*z+2 := by omega
  change sideBit ([false,false,false] ++
    (List.replicate (3*z+2) true ++
      List.drop 1 (s0RightFacing (2^z-1)))) i = true
  rw [sideBit_append_right [false,false,false]
    (List.replicate (3*z+2) true ++
      List.drop 1 (s0RightFacing (2^z-1))) i (by simp; omega)]
  have hlen0 : ([false,false,false] : List Bool).length = 3 := by rfl
  rw [hlen0]
  rw [sideBit_append_left (List.replicate (3*z+2) true)
    (List.drop 1 (s0RightFacing (2^z-1))) (i-3) (by simp; omega)]
  exact sideBit_replicate_true (3*z+2) (i-3) hidx

private theorem firstQ4P1Output_right_unchanged
    (L A z i : Nat) (hi : 3*z+5≤i) :
    (firstQ4P1Output L A z).tape (2+(i:Int)) =
      firstQ4P1SecondDrainTape L A z (2+(i:Int)) := by
  have hframe :
      q4S0Final4Inside (2+(i:Int)-3) = false := by
    simp [q4S0Final4Inside]
    omega
  have hsweep :
      s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z)
        (3*z+5) (2+(i:Int)) =
      firstQ4P1SecondDrainTape L A z (2+(i:Int)) := by
    rw [firstQ4P1SweepCell]
    have hne : (2+(i:Int)) ≠ 4 := by omega
    have hnot :
        ¬ (5 ≤ 2+(i:Int) ∧ 2+(i:Int) ≤ 3*z+6) := by omega
    simp [hne,hnot]
  simp [firstQ4P1Output,q4FrameAt_tape,hframe,hsweep]

private theorem firstQ4P1Output_right_sweep_ones
    (L A z i : Nat) (hi : 3≤i) (hi' : i≤3*z+4) :
    (firstQ4P1Output L A z).tape (2+(i:Int)) = true := by
  have hframe :
      q4S0Final4Inside (2+(i:Int)-3) = false := by
    simp [q4S0Final4Inside]
    omega
  have hsweep :
      s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z)
        (3*z+5) (2+(i:Int)) = true := by
    rw [firstQ4P1SweepCell]
    have hne : (2+(i:Int)) ≠ 4 := by omega
    have hrange :
        5 ≤ 2+(i:Int) ∧ 2+(i:Int) ≤ 3*z+6 := by omega
    simp [hne,hrange]
  simp [firstQ4P1Output,q4FrameAt_tape,hframe,hsweep]

/-- Every cell on the right-facing side of the actual q4FrameAt output
matches the canonical P1 right side. -/
theorem firstQ4P1Output_right_cell (L A z : Nat) (i : Nat) :
    (firstQ4P1Output L A z).tape (2+(i:Int)) =
      sideBit (firstQ4P1Right z) i := by
  by_cases hi0 : i=0
  · subst i
    simp [firstQ4P1Output,q4FrameAt_tape,q4S0Final4Inside,
      q4S0Final4End,firstQ4P1OutputRightSide,sideBit]
  · by_cases hi1 : i=1
    · subst i
      simp [firstQ4P1Output,q4FrameAt_tape,q4S0Final4Inside,
        q4S0Final4End,firstQ4P1OutputRightSide,sideBit]
    · by_cases hi2 : i=2
      · subst i
        have hframe :
            q4S0Final4Inside (2+(2:Int)-3) = false := by
          simp [q4S0Final4Inside]
        have hsweep :
            s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z)
              (3*z+5) (2+(2:Int)) = false := by
          rw [firstQ4P1SweepCell]
          simp
        simp [firstQ4P1Output,q4FrameAt_tape,hframe,hsweep,
          firstQ4P1Right,sideBit]
      · have hi3 : 3≤i := by omega
        by_cases hSweep : i≤3*z+4
        · calc
            (firstQ4P1Output L A z).tape (2+(i:Int)) = true :=
              firstQ4P1Output_right_sweep_ones L A z i hi3 hSweep
            _ = sideBit (firstQ4P1OutputRightSide z) i :=
              (firstQ4P1OutputRightSide_ones z i hi3 hSweep).symm
            _ = sideBit (firstQ4P1Right z) i :=
              (firstQ4P1OutputRightSide_eq_target_sideBit z i).symm
        · have hlarge : 3*z+5≤i := by omega
          have hunchanged :=
            firstQ4P1Output_right_unchanged L A z i hlarge
          let j : Nat := i-(3*z+4)
          have hcoord :
              (3*z+5:Int)+1+(j:Int) = 2+(i:Int) := by
            dsimp [j]
            omega
          have hcell := s0Config_right_cell
            (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5) j
          rw [hcoord] at hcell
          have hT :
              firstQ4P1SecondDrainTape L A z (2+(i:Int)) =
                sideBit (s0RightFacing (2^z-1)) j := by
            simpa [firstQ4P1SecondDrainTape] using hcell
          have hside :
              sideBit (firstQ4P1OutputRightSide z) i =
                sideBit (s0RightFacing (2^z-1)) j := by
            change sideBit ([false,false,false] ++
              (List.replicate (3*z+2) true ++
                List.drop 1 (s0RightFacing (2^z-1)))) i = _
            rw [sideBit_append_right [false,false,false]
              (List.replicate (3*z+2) true ++
                List.drop 1 (s0RightFacing (2^z-1))) i (by simp; omega)]
            have hlen0 : ([false,false,false] : List Bool).length = 3 := by rfl
            rw [hlen0]
            rw [sideBit_append_right (List.replicate (3*z+2) true)
              (List.drop 1 (s0RightFacing (2^z-1))) (i-3) (by simp; omega)]
            have hlenRep :
                (List.replicate (3*z+2) true).length = 3*z+2 := by simp
            rw [hlenRep]
            have hidx : i-3-(3*z+2) = i-(3*z+5) := by omega
            rw [hidx,sideBit_drop_one]
            have hidx' : i-(3*z+5)+1 = j := by
              dsimp [j]
              omega
            rw [hidx']
          calc
            (firstQ4P1Output L A z).tape (2+(i:Int)) =
                firstQ4P1SecondDrainTape L A z (2+(i:Int)) := hunchanged
            _ = sideBit (s0RightFacing (2^z-1)) j := hT
            _ = sideBit (firstQ4P1OutputRightSide z) i := hside.symm
            _ = sideBit (firstQ4P1Right z) i :=
                (firstQ4P1OutputRightSide_eq_target_sideBit z i).symm

#print axioms firstQ4P1Output_right_cell

end BB6Coverage.Agent42FirstQ4P1FrameRight

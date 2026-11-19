import FirstQ4CheckpointPostlude
import FirstQ4P1Arithmetic
import Lean.Elab.Tactic.Omega

/-!
# Left-facing cell proof for the first q4 frame → P1 tape bridge

This file proves the left-side pointwise identity for the actual
q4FrameAt output.  The right-side identity and final Config/tape
extensionality remain separate obligations.  It is an intermediate
source draft until locally compiled in the complete source closure.
-/

namespace BB6Coverage.Agent42FirstQ4P1FrameLeft

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24FirstQ4Checkpoint
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent6Q4Prefix

def firstQ4P1SecondDrainTape (L A z : Nat) : Int → Bool :=
  (s0Config (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5)).tape

def firstQ4P1Output (L A z : Nat) : Config :=
  q4FrameAt
    (s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z) (3*z+5))
    3 q4S0Final4Inside q4S0Final4End

theorem firstQ4P1SweepCell (L A z : Nat) (x : Int) :
    s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z) (3*z+5) x =
      if x = 4 then false
      else if 5 ≤ x ∧ x ≤ 3*z+6 then true
      else firstQ4P1SecondDrainTape L A z x := by
  have hshift := s0LeftSweep_shift (3*z+2)
    (firstQ4P1SecondDrainTape L A z) (3*z+5) (by omega) x
  have h1 : (3*z+5:Int) - (3*z+2:Int) + 1 = 4 := by omega
  have h2 : (3*z+5:Int) - (3*z+2:Int) + 2 = 5 := by omega
  have h3 : (3*z+5:Int) + 1 = 3*z+6 := by omega
  simpa [h1,h2,h3] using hshift

/-- Every cell on the left-facing side of the actual q4FrameAt output
matches the root checkpoint's canonical left side. -/
theorem firstQ4P1Output_left_cell (L A z : Nat) (i : Nat) :
    (firstQ4P1Output L A z).tape (1-(i:Int)) =
      sideBit (firstQ4P1Left L A) i := by
  by_cases hi0 : i = 0
  · subst i
    simp [firstQ4P1Output, q4FrameAt_tape, q4S0Final4Inside,
      q4S0Final4End, firstQ4P1Left]
  · by_cases hi1 : i = 1
    · subst i
      simp [firstQ4P1Output, q4FrameAt_tape, q4S0Final4Inside,
        q4S0Final4End, firstQ4P1Left]
    · by_cases hi2 : i = 2
      · subst i
        have hsweep :
            s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z)
              (3*z+5) (-1) =
              firstQ4P1SecondDrainTape L A z (-1) := by
          rw [firstQ4P1SweepCell]
          simp
        have hcell := s0Config_left_cell (firstQ4Left2 L A) z 0
          (2^z-1) (3*z+5) (3*z+6)
        have hcoord : (3*z+5:Int) - (3*z+6:Int) = -1 := by omega
        rw [hcoord] at hcell
        have hleft :
            s0LeftFacing (firstQ4Left2 L A) z 0 =
              d1pow z ++ firstQ4Left2 L A := by
          simp [s0LeftFacing, binDec_zero]
        rw [hleft] at hcell
        have hsplit :
            sideBit (d1pow z ++ firstQ4Left2 L A) (3*z+6) =
              sideBit (firstQ4Left2 L A) 6 := by
          rw [sideBit_append_right (d1pow z) (firstQ4Left2 L A)
            (3*z+6) (by rw [d1pow_length]; omega)]
          rw [d1pow_length]
          omega
        have hval : sideBit (firstQ4Left2 L A) 6 = true := by
          simp [firstQ4Left2, markerWord, d0, sideBit]
        have hT : firstQ4P1SecondDrainTape L A z (-1) = true := by
          calc
            firstQ4P1SecondDrainTape L A z (-1) =
                sideBit (d1pow z ++ firstQ4Left2 L A) (3*z+6) := by
                  simpa [firstQ4P1SecondDrainTape] using hcell
            _ = true := by rw [hsplit,hval]
        calc
          (firstQ4P1Output L A z).tape (-1) =
              firstQ4P1SecondDrainTape L A z (-1) := by
                simp [firstQ4P1Output, q4FrameAt_tape,
                  q4S0Final4Inside, q4S0Final4End, hsweep,
                  firstQ4P1SecondDrainTape]
          _ = true := hT
          _ = sideBit (firstQ4P1Left L A) 2 := by
                simp [firstQ4P1Left, sideBit]
      · have hi3 : 3 ≤ i := by omega
        have hframe :
            q4S0Final4Inside (1-(i:Int)-3) = false := by
          simp [q4S0Final4Inside]
          omega
        have hsweep :
            s0LeftSweep (3*z+2) (firstQ4P1SecondDrainTape L A z)
              (3*z+5) (1-(i:Int)) =
              firstQ4P1SecondDrainTape L A z (1-(i:Int)) := by
          rw [firstQ4P1SweepCell]
          have hne : 1-(i:Int) ≠ 4 := by omega
          have hrange :
              ¬ (5 ≤ 1-(i:Int) ∧ 1-(i:Int) ≤ 3*z+6) := by omega
          simp [hne,hrange]
        have hcell := s0Config_left_cell (firstQ4Left2 L A) z 0
          (2^z-1) (3*z+5) (3*z+4+i)
        have hcoord :
            (3*z+5:Int) - (3*z+4+i:Int) = 1-(i:Int) := by omega
        rw [hcoord] at hcell
        have hleft :
            s0LeftFacing (firstQ4Left2 L A) z 0 =
              d1pow z ++ firstQ4Left2 L A := by
          simp [s0LeftFacing, binDec_zero]
        rw [hleft] at hcell
        have hsplit1 :
            sideBit (d1pow z ++ firstQ4Left2 L A) (3*z+4+i) =
              sideBit (firstQ4Left2 L A) (4+i) := by
          rw [sideBit_append_right (d1pow z) (firstQ4Left2 L A)
            (3*z+4+i) (by rw [d1pow_length]; omega)]
          rw [d1pow_length]
          omega
        have hprefix :
            firstQ4Left2 L A =
              (markerWord 2 ++ d0) ++
                (binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh) := by
          simp [firstQ4Left2, List.append_assoc]
        have hlen : (markerWord 2 ++ d0).length = 7 := by
          simp [markerWord,d0]
        have hsplit2 :
            sideBit (firstQ4Left2 L A) (4+i) =
              sideBit
                (binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh)
                (i-3) := by
          rw [hprefix]
          rw [sideBit_append_right (markerWord 2 ++ d0)
            (binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh)
            (4+i) (by rw [hlen]; omega)]
          rw [hlen]
          omega
        have htarget :
            sideBit (firstQ4P1Left L A) i =
              sideBit
                (binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh)
                (i-3) := by
          unfold firstQ4P1Left
          rw [sideBit_append_right [false,true,true]
            (binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh)
            i (by simp; omega)]
        calc
          (firstQ4P1Output L A z).tape (1-(i:Int)) =
              firstQ4P1SecondDrainTape L A z (1-(i:Int)) := by
                simp [firstQ4P1Output, q4FrameAt_tape,
                  hframe, hsweep, firstQ4P1SecondDrainTape]
          _ = sideBit (d1pow z ++ firstQ4Left2 L A) (3*z+4+i) := by
                simpa [firstQ4P1SecondDrainTape] using hcell
          _ = sideBit (firstQ4Left2 L A) (4+i) := hsplit1
          _ = sideBit
                (binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh)
                (i-3) := hsplit2
          _ = sideBit (firstQ4P1Left L A) i := htarget.symm

#print axioms firstQ4P1Output_left_cell

end BB6Coverage.Agent42FirstQ4P1FrameLeft

import PositiveZCheckpointSetupAllGuards
import Lean.Elab.Tactic.Omega

/-!
# Source-exact two-scan root prefix for the positive-z setup macro

This file closes the missing link between the genuine S0 source configuration
and the post-two-scan tape consumed by Agent 48's positive-z setup suffix.
The first sweep is counted by the original TM2 table, B8 is the exact finite
bridge, and the second sweep is again counted by the original table.
No finite-tape approximation is used.
-/

namespace BB6Coverage.Agent48PositiveZSetupRootPrefix

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent48PositiveZSetup
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42PositiveZSetupBlanks
open BB6Coverage.Agent42PositiveZSetupFirstGuards
open BB6Coverage.Agent42PositiveZSetupAllGuards

set_option maxHeartbeats 4000000

private theorem sideBit_d1pow_all (n i : Nat) (hi : i < 3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [d1pow,d1,sideBit]
      | succ i =>
          cases i with
          | zero => simp [d1pow,d1,sideBit]
          | succ i =>
              cases i with
              | zero => simp [d1pow,d1,sideBit]
              | succ i =>
                  have hi' : i < 3*n := by omega
                  simpa [d1pow,d1,sideBit] using ih i hi'

private theorem setupPrefixInput_leftFacing_ones
    (L A i : Nat) (hi : i < 3*A+1) :
    sideBit (setupPrefixInputLeftFacing L A) i = true := by
  have hprefix :
      setupPrefixInputLeftFacing L A =
        d1pow A ++ (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) := by
    simp [setupPrefixInputLeftFacing,List.append_assoc]
  by_cases hlt : i < 3*A
  · rw [hprefix]
    rw [sideBit_append_left (d1pow A)
      (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) i
      (by rw [d1pow_length]; omega)]
    exact sideBit_d1pow_all A i hlt
  · have heq : i = 3*A := by omega
    subst i
    rw [hprefix]
    rw [sideBit_append_right (d1pow A)
      (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) (3*A)
      (by rw [d1pow_length]; omega)]
    simp [d1pow_length,markerWord,sideBit]

private theorem setupPrefixInput_left_d0_cell
    (L A j : Nat) (hj : j < 3) :
    sideBit (setupPrefixInputLeftFacing L A) (3*A+3+j) =
      sideBit d0 j := by
  rw [show setupPrefixInputLeftFacing L A =
      d1pow A ++ (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) by
        simp [setupPrefixInputLeftFacing,List.append_assoc]]
  have hlenA : (d1pow A).length = 3*A := d1pow_length A
  have hlenM : (markerWord 1).length = 3 := by simp [markerWord]
  have h1 : (d1pow A).length ≤ 3*A+3+j := by rw [hlenA]; omega
  rw [sideBit_append_right (d1pow A)
    (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) (3*A+3+j) h1]
  have hidx1 : 3*A+3+j-(d1pow A).length = 3+j := by
    rw [hlenA]
    omega
  rw [hidx1]
  have h2 : (markerWord 1).length ≤ 3+j := by rw [hlenM]; omega
  rw [sideBit_append_right (markerWord 1) (d0 ++ (d1pow L ++ lh))
    (3+j) h2]
  have hidx2 : 3+j-(markerWord 1).length = j := by
    rw [hlenM]
    omega
  rw [hidx2]
  exact sideBit_append_left d0 (d1pow L ++ lh) j (by simpa [d0] using hj)

private theorem setupPrefixInput_left_marker_cell
    (L A j : Nat) (hj : j < 3) :
    sideBit (setupPrefixInputLeftFacing L A) (3*A+j) =
      sideBit (markerWord 1) j := by
  rw [show setupPrefixInputLeftFacing L A =
      d1pow A ++ (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) by
        simp [setupPrefixInputLeftFacing,List.append_assoc]]
  have hlenA : (d1pow A).length = 3*A := d1pow_length A
  have h1 : (d1pow A).length ≤ 3*A+j := by rw [hlenA]; omega
  rw [sideBit_append_right (d1pow A)
    (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) (3*A+j) h1]
  have hidx : 3*A+j-(d1pow A).length=j := by rw [hlenA]; omega
  rw [hidx]
  exact sideBit_append_left (markerWord 1) (d0 ++ (d1pow L ++ lh)) j
    (by simpa [markerWord] using hj)

private theorem setupPrefixInput_left_d1powL_cell
    (L A i : Nat) (hi : i < 3*L) :
    sideBit (setupPrefixInputLeftFacing L A) (3*A+6+i) =
      sideBit (d1pow L) i := by
  rw [show setupPrefixInputLeftFacing L A =
      d1pow A ++ (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) by
        simp [setupPrefixInputLeftFacing,List.append_assoc]]
  have hlenA : (d1pow A).length = 3*A := d1pow_length A
  have hlenM : (markerWord 1).length = 3 := by simp [markerWord]
  have hlen0 : d0.length = 3 := by rfl
  have h1 : (d1pow A).length ≤ 3*A+6+i := by rw [hlenA]; omega
  rw [sideBit_append_right (d1pow A)
    (markerWord 1 ++ (d0 ++ (d1pow L ++ lh))) (3*A+6+i) h1]
  have hidx1 : 3*A+6+i-(d1pow A).length = 6+i := by
    rw [hlenA]
    omega
  rw [hidx1]
  have h2 : (markerWord 1).length ≤ 6+i := by rw [hlenM]; omega
  rw [sideBit_append_right (markerWord 1) (d0 ++ (d1pow L ++ lh))
    (6+i) h2]
  have hidx2 : 6+i-(markerWord 1).length = 3+i := by
    rw [hlenM]
    omega
  rw [hidx2]
  have h3 : d0.length ≤ 3+i := by rw [hlen0]; omega
  rw [sideBit_append_right d0 (d1pow L ++ lh) (3+i) h3]
  have hidx3 : 3+i-d0.length=i := by rw [hlen0]; omega
  rw [hidx3]
  exact sideBit_append_left (d1pow L) lh i (by rw [d1pow_length]; exact hi)

private theorem setupPrefixInput_left_lh_cell
    (L A j : Nat) :
    sideBit (setupPrefixInputLeftFacing L A) (3*A+6+3*L+j) =
      sideBit lh j := by
  let xs := d1pow A ++ markerWord 1 ++ d0 ++ d1pow L
  have hlen : xs.length = 3*A+6+3*L := by
    simp [xs,d1pow_length,markerWord,d0,List.append_assoc] <;> omega
  have h := sideBit_append_right xs lh (3*A+6+3*L+j)
    (by rw [hlen]; omega)
  rw [hlen] at h
  have hidx : 3*A+6+3*L+j-(3*A+6+3*L)=j := by omega
  rw [hidx] at h
  simpa [setupPrefixInputLeftFacing,xs,List.append_assoc] using h

private theorem setupPrefixInput_leftOnes (L A z : Nat) :
    leftOnes (setupPrefixInputTape L A z) 0 (3*A+1) := by
  intro i hi
  have hcell := setupPrefixInput_left_cell L A z i
  have hword := setupPrefixInput_leftFacing_ones L A i hi
  simpa [leftOnes] using hcell.trans hword

private theorem setupPrefixInput_rightZero (L A z : Nat) :
    setupPrefixInputTape L A z 1 = false := by
  have hcell := s0Config_right_cell
    (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 0
  simpa [setupPrefixInputTape,s0RightFacing,sideBit] using hcell

private theorem setupPrefixSweep_outside
    (A : Nat) (T : Int → Bool) (x : Int)
    (hne : x ≠ -(3*A:Int))
    (hnot : ¬ (-(3*A:Int)+1 ≤ x ∧ x ≤ 1)) :
    sweptLeft (3*A+1) T 0 x = T x := by
  rw [sweptLeft_shift (3*A) T 0 x]
  have hclear : (0:Int) - (↑(3*A)+1) + 1 = -(↑(3*A)) := by omega
  have hlower : (0:Int) - (↑(3*A)+1) + 2 = -(↑(3*A))+1 := by omega
  rw [hclear,hlower]
  simp [hne,hnot]

private theorem setupPrefixSweep_clear
    (A : Nat) (T : Int → Bool) :
    sweptLeft (3*A+1) T 0 (-(3*A:Int)) = false := by
  rw [sweptLeft_shift (3*A) T 0 (-(3*A:Int))]
  have hclear : (0:Int) - (↑(3*A)+1) + 1 = -(↑(3*A)) := by omega
  have hlower : (0:Int) - (↑(3*A)+1) + 2 = -(↑(3*A))+1 := by omega
  rw [hclear,hlower]
  simp

private theorem setupPrefixFirstSweep_b8Input (L A z : Nat) :
    setupB8Input (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
      (-(3*A+1:Int)) := by
  unfold setupB8Input
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hout := setupPrefixSweep_outside A (setupPrefixInputTape L A z)
      (-(3*A+4:Int)) (by omega) (by omega)
    have hcell := setupPrefixInput_left_cell L A z (3*A+4)
    have hw := setupPrefixInput_left_d0_cell L A 1 (by omega)
    have hfalse :
        sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0
          (-(3*A+4:Int)) = false := by
      rw [hout]
      have hcell' :
          setupPrefixInputTape L A z (-(3*A+4:Int)) =
            sideBit (setupPrefixInputLeftFacing L A) (3*A+4) := by
        simpa [Int.natCast_add,Int.natCast_mul] using hcell
      have hw' :
          sideBit (setupPrefixInputLeftFacing L A) (3*A+4) = false := by
        rw [show 3*A+3+1 = 3*A+4 by omega] at hw
        simpa [d0,sideBit] using hw
      rw [hcell']
      exact hw'
    have hcoord : (-(3*A+1:Int) + (-3:Int)) = -(3*A+4:Int) := by omega
    exact (congrArg (fun x : Int =>
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x) hcoord).trans hfalse
  · have hout := setupPrefixSweep_outside A (setupPrefixInputTape L A z)
      (-(3*A+3:Int)) (by omega) (by omega)
    have hcell := setupPrefixInput_left_cell L A z (3*A+3)
    have hw := setupPrefixInput_left_d0_cell L A 0 (by omega)
    have hfalse :
        sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0
          (-(3*A+3:Int)) = false := by
      rw [hout]
      have hcell' :
          setupPrefixInputTape L A z (-(3*A+3:Int)) =
            sideBit (setupPrefixInputLeftFacing L A) (3*A+3) := by
        simpa [Int.natCast_add,Int.natCast_mul] using hcell
      have hw' :
          sideBit (setupPrefixInputLeftFacing L A) (3*A+3) = false := by
        rw [show 3*A+3+0 = 3*A+3 by omega] at hw
        simpa [d0,sideBit] using hw
      rw [hcell']
      exact hw'
    have hcoord : (-(3*A+1:Int) + (-2:Int)) = -(3*A+3:Int) := by omega
    exact (congrArg (fun x : Int =>
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x) hcoord).trans hfalse
  · have hout := setupPrefixSweep_outside A (setupPrefixInputTape L A z)
      (-(3*A+2:Int)) (by omega) (by omega)
    have hcell := setupPrefixInput_left_cell L A z (3*A+2)
    have hw := setupPrefixInput_left_marker_cell L A 2 (by omega)
    have htrue :
        sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0
          (-(3*A+2:Int)) = true := by
      rw [hout]
      have hcell' :
          setupPrefixInputTape L A z (-(3*A+2:Int)) =
            sideBit (setupPrefixInputLeftFacing L A) (3*A+2) := by
        simpa [Int.natCast_add,Int.natCast_mul] using hcell
      have hw' :
          sideBit (setupPrefixInputLeftFacing L A) (3*A+2) = true := by
        simpa [markerWord,sideBit] using hw
      rw [hcell']
      exact hw'
    have hcoord : (-(3*A+1:Int) + (-1:Int)) = -(3*A+2:Int) := by omega
    exact (congrArg (fun x : Int =>
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x) hcoord).trans htrue
  · have hout := setupPrefixSweep_outside A (setupPrefixInputTape L A z)
      (-(3*A+1:Int)) (by omega) (by omega)
    have hcell := setupPrefixInput_left_cell L A z (3*A+1)
    have hw := setupPrefixInput_left_marker_cell L A 1 (by omega)
    have hfalse :
        sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0
          (-(3*A+1:Int)) = false := by
      rw [hout]
      have hcell' :
          setupPrefixInputTape L A z (-(3*A+1:Int)) =
            sideBit (setupPrefixInputLeftFacing L A) (3*A+1) := by
        simpa [Int.natCast_add,Int.natCast_mul] using hcell
      have hw' :
          sideBit (setupPrefixInputLeftFacing L A) (3*A+1) = false := by
        simpa [markerWord,sideBit] using hw
      rw [hcell']
      exact hw'
    exact hfalse
  · have hfalse := setupPrefixSweep_clear A (setupPrefixInputTape L A z)
    have hcoord : (-(3*A+1:Int) + 1) = -(3*A:Int) := by omega
    exact (congrArg (fun x : Int =>
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x) hcoord).trans hfalse

private theorem setupPrefixAfterB8_left_cell
    (L A z i : Nat) :
    setupPrefixAfterB8 L A z (-(3*A+3+i:Int)) =
      if i<2 then true
      else setupPrefixInputTape L A z (-(3*A+3+i:Int)) := by
  rw [setupPrefixAfterB8,q4FrameAt_tape]
  have hcoord :
      (-(3*A+3+i:Int))-(-(3*A+1:Int)) = -2-(i:Int) := by omega
  rw [hcoord]
  by_cases hi : i<2
  · have hcase : i=0 ∨ i=1 := by omega
    rcases hcase with rfl | rfl <;> simp [setupB8Inside,setupB8End]
  · have hnot : setupB8Inside (-2-(i:Int)) = false := by
      simp [setupB8Inside]
      omega
    simp [hnot,hi]

private theorem setupPrefixAfterB8_leftOnes (L A z : Nat) :
    leftOnes (setupPrefixAfterB8 L A z) (-(3*A+3:Int)) (3*L+5) := by
  unfold leftOnes
  intro i hi
  have hcoord :
      (-(3*A+3:Int)-(i:Int)) = -(3*A+3+i:Int) := by omega
  rw [hcoord]
  rw [setupPrefixAfterB8_left_cell]
  by_cases h0 : i<2
  · simp [h0]
  · have hinput := setupPrefixInput_left_cell L A z (3*A+3+i)
    have hword :
        sideBit (setupPrefixInputLeftFacing L A) (3*A+3+i) = true := by
      by_cases h2 : i=2
      · subst i
        have h := setupPrefixInput_left_d0_cell L A 2 (by omega)
        simpa [d0,sideBit] using h
      · by_cases hmid : i<3*L+3
        · let j := i-3
          have hj : j<3*L := by dsimp [j]; omega
          have h := setupPrefixInput_left_d1powL_cell L A j hj
          have hindex : 3*A+3+i = 3*A+6+j := by dsimp [j]; omega
          rw [hindex]
          rw [h]
          exact sideBit_d1pow_all L j hj
        · by_cases hlast0 : i=3*L+3
          · subst i
            have h := setupPrefixInput_left_lh_cell L A 0
            have hindex : 3*A+3+(3*L+3) = 3*A+6+3*L+0 := by omega
            rw [hindex]
            simpa [lh,sideBit] using h
          · have hlast1 : i=3*L+4 := by omega
            subst i
            have h := setupPrefixInput_left_lh_cell L A 1
            have hindex : 3*A+3+(3*L+4) = 3*A+6+3*L+1 := by omega
            rw [hindex]
            simpa [lh,sideBit] using h
    rw [hinput]
    exact hword

private theorem setupPrefixAfterB8_rightZero (L A z : Nat) :
    setupPrefixAfterB8 L A z (-(3*A+2:Int)) = false := by
  rw [setupPrefixAfterB8,q4FrameAt_tape]
  have hcoord :
      (-(3*A+2:Int))-(-(3*A+1:Int)) = -1 := by omega
  rw [hcoord]
  simp [setupB8Inside,setupB8End]

/-- The exact first-scan, B8, second-scan execution from the genuine S0
source configuration to the post-two-scan tape used by the setup suffix. -/
theorem positiveZSetupPrefix_run (L A z : Nat) :
    run tm2
      (3*(3*A+1)+8+3*(3*L+5))
      (s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0) =
      some ⟨3,setupPrefixHead A L,setupPrefixAfterScans L A z⟩ := by
  let T := setupPrefixInputTape L A z
  have hstart :
      s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 =
        ⟨3,0,T⟩ := by
    simp [T,setupPrefixInputTape,s0Config]
  have hfirst := counted_left_sweep (3*A+1) T 0
    (setupPrefixInput_leftOnes L A z) (setupPrefixInput_rightZero L A z)
  have hB8 := setupB8_at (sweptLeft (3*A+1) T 0)
    (-(3*A+1:Int)) (setupPrefixFirstSweep_b8Input L A z)
  have hB8Head : (-(3*A+1:Int)+(-2:Int)) = -(3*A+3:Int) := by omega
  have hB8' :
      run tm2 8 ⟨3,-(3*A+1:Int),sweptLeft (3*A+1) T 0⟩ =
        some ⟨3,-(3*A+3:Int),setupPrefixAfterB8 L A z⟩ := by
    simpa [T,setupPrefixAfterB8,q4FrameAt,shiftConfig,embed,setupB8End,hB8Head] using hB8
  have hfirstB8 := run_append_some hfirst hB8'
  have hsecond := counted_left_sweep (3*L+5)
    (setupPrefixAfterB8 L A z) (-(3*A+3:Int))
    (setupPrefixAfterB8_leftOnes L A z)
    (setupPrefixAfterB8_rightZero L A z)
  have htotal := run_append_some hfirstB8 hsecond
  have hhead :
      (-(3*A+3:Int)-(3*L+5:Int)) = setupPrefixHead A L := by
    dsimp [setupPrefixHead]
    omega
  rw [hstart]
  simpa [setupPrefixAfterScans_eq,hhead] using htotal

#print axioms positiveZSetupPrefix_run

end BB6Coverage.Agent48PositiveZSetupRootPrefix

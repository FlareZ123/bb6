import FirstQ4CheckpointPrePostlude
import Q4S0FirstCycleMacros
import Lean.Elab.Tactic.Omega

/-!
# Source composition through the first positive-z q4 checkpoint

The first three phases are already isolated in
`FirstQ4CheckpointPrePostlude`: the arbitrary-value S0 drain, the
source-level Rst1' macro, and the all-ones S0 drain.  This module closes
the final `9*z+10` postlude using Agent 48's arbitrary-tape q4/S0 macro.

The result is an exact original-TM2 run to the q4 finite frame.  The
transitive Lean source closure and axiom profile still require acceptance;
this file is deliberately in im-results/.
-/

namespace BB6Coverage.Agent42FirstQ4Checkpoint

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent24FirstQ4Checkpoint
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48Q4S0Macros

/-- The source tape at the output of the second S0 drain. -/
private def secondDrainTape (L A z : Nat) : Int → Bool :=
  (s0Config (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5)).tape

/-- The second-drain output has the exact d1^z ++ marker-2 left-facing
prefix.  Its first 3z+2 cells are therefore ones. -/
private theorem secondDrain_leftOnes (L A z : Nat) :
    s0LeftOnes (secondDrainTape L A z) (3*z+5) (3*z+2) := by
  let T := secondDrainTape L A z
  let h : Int := (3*z+5)
  have hleft :
      s0LeftFacing (firstQ4Left2 L A) z 0 =
        d1pow z ++ firstQ4Left2 L A := by
    simp [s0LeftFacing, binDec_zero]
  intro i hi
  have hcell := s0Config_left_cell
    (firstQ4Left2 L A) z 0 (2^z-1) h i
  rw [hleft] at hcell
  have hside :
      sideBit (d1pow z ++ firstQ4Left2 L A) i = true := by
    rw [sideBit_append, d1pow_length]
    by_cases hlt : i < 3*z
    · simp [hlt, sideBit_d1pow_true z i hlt]
    · have hcases : i = 3*z ∨ i = 3*z+1 := by omega
      rcases hcases with hcase | hcase
      · subst i
        simp [firstQ4Left2, markerWord, d0, sideBit]
      · subst i
        simp [firstQ4Left2, markerWord, d0, sideBit]
  change T (h-(i:Int)) = true
  calc
    T (h-(i:Int)) =
        sideBit (d1pow z ++ firstQ4Left2 L A) i := by
          simpa [T, secondDrainTape, h] using hcell
    _ = true := hside

/-- The first cell to the right of the second-drain head is the required
zero sentinel for the q4/S0 left-one scan. -/
private theorem secondDrain_rightZero (L A z : Nat) :
    secondDrainTape L A z ((3*z+5:Int)+1) = false := by
  have hcell := s0Config_right_cell
    (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5) 0
  simpa [secondDrainTape, s0RightFacing, sideBit] using hcell

/-- The six cells immediately beyond d1^z are the fixed marker-2/d0
boundary 1,1,0,1,0,0.  The q4 postlude consumes the first two ones; the
remaining four bits are exactly its final-four input 0,1,0,0. -/
private theorem secondDrain_boundary (L A : Nat) :
    sideBit (firstQ4Left2 L A) 0 = true ∧
    sideBit (firstQ4Left2 L A) 1 = true ∧
    sideBit (firstQ4Left2 L A) 2 = false ∧
    sideBit (firstQ4Left2 L A) 3 = true ∧
    sideBit (firstQ4Left2 L A) 4 = false ∧
    sideBit (firstQ4Left2 L A) 5 = false := by
  simp [firstQ4Left2, markerWord, d0, sideBit]

/-- Package the four-cell input guard after the q4/S0 counted left sweep. -/
private theorem secondDrain_final4Input (L A z : Nat) :
    q4S0Final4Input
      (s0LeftSweep (3*z+2) (secondDrainTape L A z) (3*z+5))
      ((3*z+5:Int)-(3*z+2)) := by
  let T := secondDrainTape L A z
  let h : Int := (3*z+5)
  let k : Nat := 3*z+2
  have hhead : h-(k:Int) = 3 := by dsimp [h,k]; omega
  have hshift := s0LeftSweep_shift k T h (by dsimp [k]; omega)
  have hunchanged (x : Int) (hx : x ≤ 3) :
      s0LeftSweep k T h x = T x := by
    rw [hshift x]
    have hlow : x ≠ h-(k:Int)+1 := by rw [hhead]; omega
    have hhigh : ¬ (h-(k:Int)+2 ≤ x ∧ x ≤ h+1) := by
      rw [hhead]
      omega
    simp [hlow, hhigh]
  have hleftCell (j : Nat) (hj : j < 6) :
      T (5-(j:Int)) = sideBit (firstQ4Left2 L A) j := by
    have hcell := s0Config_left_cell
      (firstQ4Left2 L A) z 0 (2^z-1) h (3*z+j)
    rw [show h-(3*z+j:Int) = 5-(j:Int) by dsimp [h]; omega] at hcell
    have hprefix :
        s0LeftFacing (firstQ4Left2 L A) z 0 =
          d1pow z ++ firstQ4Left2 L A := by
      simp [s0LeftFacing, binDec_zero]
    rw [hprefix] at hcell
    have hside :
        sideBit (d1pow z ++ firstQ4Left2 L A) (3*z+j) =
          sideBit (firstQ4Left2 L A) j := by
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right]
      · have hlen := d1pow_length z
        rw [hlen]
        omega
      · rw [d1pow_length]
        omega
    calc
      T (5-(j:Int)) =
          sideBit (d1pow z ++ firstQ4Left2 L A) (3*z+j) := by
            simpa [T, secondDrainTape] using hcell
      _ = sideBit (firstQ4Left2 L A) j := hside
  have hbits := secondDrain_boundary L A
  rw [hhead]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hunchanged 0 (by omega)]
    have h := hleftCell 5 (by omega)
    simpa [hbits.2.2.2] using h
  · rw [hunchanged 1 (by omega)]
    have h := hleftCell 4 (by omega)
    simpa [hbits.2.2.1] using h
  · rw [hunchanged 2 (by omega)]
    have h := hleftCell 3 (by omega)
    simpa [hbits.2.1] using h
  · rw [hunchanged 3 (by omega)]
    have h := hleftCell 2 (by omega)
    simpa [hbits.1] using h

/-- Exact final postlude: the scan of 3z+2 left ones and the fixed
four-step state-4 return take 9z+10 primitive transitions. -/
theorem firstQ4Checkpoint_postlude (L A z : Nat) :
    run tm2 (9*z+10)
      (s0Config (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5)) =
    some (q4FrameAt
      (s0LeftSweep (3*z+2)
        (s0Config (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5)).tape
        (3*z+5))
      3 q4S0Final4Inside q4S0Final4End) := by
  let T := secondDrainTape L A z
  let h : Int := (3*z+5)
  let k : Nat := 3*z+2
  have hones := secondDrain_leftOnes L A z
  have hright := secondDrain_rightZero L A z
  have hguard := secondDrain_final4Input L A z
  have hpost := q4S0Postlude_at k T h hones hright hguard
  have hcost : 3*k+4 = 9*z+10 := by dsimp [k]; omega
  have hhead : h-(k:Int) = 3 := by dsimp [h,k]; omega
  change run tm2 (9*z+10) ⟨3,h,T⟩ =
    some (q4FrameAt (s0LeftSweep k T h) 3
      q4S0Final4Inside q4S0Final4End)
  rw [← hcost]
  simpa [hhead] using hpost

/-- Exact original-TM2 run from the marker-1 S0 input to the first q4
checkpoint frame.  This composes the general S0 drain, the existing
Rst1' counted macro, the second all-ones S0 drain, and the q4/S0 postlude. -/
theorem firstQ4Checkpoint_run (L A z : Nat) (hz : z < 2^A) :
    run tm2
      ((drainCost z 0 +
        ((97+12*(L+A)+3*z) +
          (6*4^z+42*2^z-12*z-48))) +
        (9*z+10))
      (s0Config (firstQ4Left0 L) A z 0 0) =
    some (q4FrameAt
      (s0LeftSweep (3*z+2)
        (s0Config (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5)).tape
        (3*z+5))
      3 q4S0Final4Inside q4S0Final4End) := by
  have hpre := firstQ4Checkpoint_prePostlude L A z hz
  have hpost := firstQ4Checkpoint_postlude L A z
  rw [run_append, hpre]
  simp only [Option.bind_some]
  exact hpost

#print axioms secondDrain_leftOnes
#print axioms secondDrain_rightZero
#print axioms secondDrain_final4Input
#print axioms firstQ4Checkpoint_postlude
#print axioms firstQ4Checkpoint_run

end BB6Coverage.Agent42FirstQ4Checkpoint

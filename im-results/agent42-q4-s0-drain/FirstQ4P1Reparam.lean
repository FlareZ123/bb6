import PositiveZFirstCycleEndpoint
import Lean.Elab.Tactic.Omega

/-!
# Reparameterize the root's first q4 checkpoint as the P1 input family

The root-side first checkpoint has left side
  011 ++ binDec (A+L+2) (M-1) ++ lh,
where M = 2^A * (2^(L+2)-1).  Agent 48's P1 input family uses
  011 ++ d0 ++ binDec w q ++ lh.

For A>0, set
  w = A+L+1,
  q = 2^(A-1)*(2^(L+2)-1)-1.
Then M-1=2*q+1, q<2^w, and the source theorem binDec_odd gives
  binDec (A+L+2) (M-1) = d0 ++ binDec w q.

This file proves that exact arithmetic/list reparameterization and
identifies the two *side encodings*.  It does NOT yet prove that the
q4FrameAt output of firstQ4Checkpoint_run is pointwise equal to this
side encoding; that remaining obligation is a tape-coordinate lemma.
All declarations here are intermediate source candidates until compiled
in the complete Lean 4.36.0-rc2 import closure.
-/

namespace BB6Coverage.Agent42FirstQ4P1Reparam

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent48PositiveZSecondCycle

def firstQ4P1M (L A : Nat) : Nat :=
  2^A * (2^(L+2)-1)

def firstQ4P1Width (L A : Nat) : Nat :=
  A+L+1

def firstQ4P1Value (L A : Nat) : Nat :=
  2^(A-1) * (2^(L+2)-1) - 1

/-- The reparameterized value fits the one-smaller BinDec width. -/
theorem firstQ4P1Value_lt (L A : Nat) (hA : 0 < A) :
    firstQ4P1Value L A < 2^(firstQ4P1Width L A) := by
  unfold firstQ4P1Value firstQ4P1Width
  have hC : 2^(L+2)-1 < 2^(L+2) :=
    Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hprod :
      2^(A-1) * (2^(L+2)-1) <
        2^(A-1) * 2^(L+2) :=
    Nat.mul_lt_mul_of_pos_left hC (Nat.pow_pos (by decide))
  have hpow :
      2^(A-1) * 2^(L+2) = 2^(A+L+1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  exact lt_of_le_of_lt (Nat.sub_le _ _) (by simpa [hpow] using hprod)

/-- The root checkpoint's odd BinDec argument is exactly 2*q+1. -/
theorem firstQ4P1Value_odd (L A : Nat) (hA : 0 < A) :
    2 * firstQ4P1Value L A + 1 = firstQ4P1M L A - 1 := by
  have hpow2 : 4 ≤ 2^(L+2) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 2 ≤ L+2 by omega)
    norm_num at h
    exact h
  have hC : 1 ≤ 2^(L+2)-1 := by omega
  have hprod : 0 < 2^(A-1) * (2^(L+2)-1) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hsub :
      (2^(A-1) * (2^(L+2)-1) - 1) + 1 =
        2^(A-1) * (2^(L+2)-1) :=
    Nat.sub_add_cancel (by omega)
  have hpowA : 2^A = 2^(A-1)*2 := by
    rw [show A = (A-1)+1 by omega, Nat.pow_succ]
  have hmul :
      2 * (2^(A-1) * (2^(L+2)-1)) =
        2^A * (2^(L+2)-1) := by
    calc
      2 * (2^(A-1) * (2^(L+2)-1)) =
          (2*2^(A-1)) * (2^(L+2)-1) :=
            (Nat.mul_assoc 2 (2^(A-1)) (2^(L+2)-1)).symm
      _ = (2^(A-1)*2) * (2^(L+2)-1) := by
            rw [Nat.mul_comm 2 (2^(A-1))]
      _ = 2^A * (2^(L+2)-1) := by rw [← hpowA]
  change
    2 * (2^(A-1) * (2^(L+2)-1) - 1) + 1 =
      2^A * (2^(L+2)-1) - 1
  omega

/-- The first q4 checkpoint's left-facing side as recorded in the
root checkpoint dossier. -/
def firstQ4P1Left (L A : Nat) : List Bool :=
  [false,true,true] ++
    binDec (A+L+2) (firstQ4P1M L A - 1) ++ lh

/-- The first q4 checkpoint's right-facing side, starting at cell 2
(head coordinate 1). -/
def firstQ4P1Right (z : Nat) : List Bool :=
  [false,false,false] ++ List.replicate (3*z+5) true ++
    [false,false] ++ d1pow (2^z) ++ [false,false,false,false]

/-- The root checkpoint left side is exactly Agent 48's P1 input side
after the parameter change (w,q)=(A+L+1,2^(A-1)*(2^(L+2)-1)-1). -/
theorem firstQ4P1Left_eq_firstCycleCheckpointLeft
    (L A : Nat) (hA : 0 < A) :
    firstQ4P1Left L A =
      firstCycleCheckpointLeft (firstQ4P1Width L A)
        (firstQ4P1Value L A) := by
  have hbin :
      binDec (A+L+2) (firstQ4P1M L A - 1) =
        d0 ++ binDec (A+L+1) (firstQ4P1Value L A) := by
    rw [show A+L+2 = (A+L+1)+1 by omega,
      ← firstQ4P1Value_odd L A hA]
    exact binDec_odd (A+L+1) (firstQ4P1Value L A)
      (firstQ4P1Value_lt L A hA)
  simp [firstQ4P1Left, firstCycleCheckpointLeft,
    firstQ4P1Width, hbin, List.append_assoc]

/-- The root checkpoint right side is definitionally Agent 48's P1
right side. -/
theorem firstQ4P1Right_eq_firstCycleCheckpointRight (z : Nat) :
    firstQ4P1Right z = firstCycleCheckpointRight z := rfl

/-- The two canonical side-based tape encodings are definitionally the
same after the parameter reindexing.  This is not yet the identification
of the actual finite-frame run output with either encoding. -/
def firstQ4P1Tape (L A z : Nat) : Int → Bool :=
  q4TapeFromSides (firstQ4P1Left L A) (firstQ4P1Right z) 1

theorem firstQ4P1Tape_eq_firstCycleCheckpointTape
    (L A z : Nat) (hA : 0 < A) :
    firstQ4P1Tape L A z =
      firstCycleCheckpointTape z (firstQ4P1Width L A)
        (firstQ4P1Value L A) := by
  unfold firstQ4P1Tape firstCycleCheckpointTape
  rw [firstQ4P1Left_eq_firstCycleCheckpointLeft L A hA,
    firstQ4P1Right_eq_firstCycleCheckpointRight z]

#print axioms firstQ4P1Value_lt
#print axioms firstQ4P1Value_odd
#print axioms firstQ4P1Left_eq_firstCycleCheckpointLeft
#print axioms firstQ4P1Tape_eq_firstCycleCheckpointTape

end BB6Coverage.Agent42FirstQ4P1Reparam

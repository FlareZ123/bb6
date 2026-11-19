import FirstQ4P1Arithmetic
import PositiveZFirstCycleEndpoint

/-!
# Identify the root first-q4 side encoding with Agent 48's P1 input

The arithmetic/BinDec identity is isolated in FirstQ4P1Arithmetic so
it can be compiled independently of this larger dependency closure.
This adapter proves only equality of the two side-based tape encodings;
the actual q4FrameAt output still needs the coordinate lemma recorded in
FirstQ4P1FrameCoordinates.md.
-/

namespace BB6Coverage.Agent42FirstQ4P1Reparam

open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent48PositiveZSecondCycle

theorem firstQ4P1Left_eq_firstCycleCheckpointLeft
    (L A : Nat) (hA : 0 < A) :
    firstQ4P1Left L A =
      firstCycleCheckpointLeft (firstQ4P1Width L A)
        (firstQ4P1Value L A) := by
  simpa [firstCycleCheckpointLeft, firstQ4P1Width,
    List.append_assoc] using firstQ4P1Left_eq_reindexed L A hA

theorem firstQ4P1Right_eq_firstCycleCheckpointRight (z : Nat) :
    firstQ4P1Right z = firstCycleCheckpointRight z := rfl

/-- Equality of the canonical side-based tape encodings after the
parameter reindexing.  This is not yet the actual run-output identity. -/
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

#print axioms firstQ4P1Left_eq_firstCycleCheckpointLeft
#print axioms firstQ4P1Tape_eq_firstCycleCheckpointTape


/-- Once the root checkpoint has been identified with its canonical
side-based tape, Agent 48's existing P1 prefix theorem applies directly.
This is a transition theorem from the side encoding, not yet from the
actual q4FrameAt output of firstQ4Checkpoint_run. -/
theorem firstQ4P1_sidePrefix_to_s0DrainInput
    (L A z : Nat) (hA : 0 < A) (hz : 1 ≤ z) :
    run tm2 (3*2^z+3*z+58)
      ⟨4,1,firstQ4P1Tape L A z⟩ =
    some (s0Config
      (firstCycleEndpointLeft z (firstQ4P1Width L A)
        (firstQ4P1Value L A))
      (2^z-1) (2^(2^z-1)-1) 0 (firstCycleEndpointHead z)) := by
  rw [firstQ4P1Tape_eq_firstCycleCheckpointTape L A z hA]
  exact firstCyclePrefix_to_s0DrainInput z
    (firstQ4P1Width L A) (firstQ4P1Value L A)
    hz (firstQ4P1Value_lt L A hA)

#print axioms firstQ4P1_sidePrefix_to_s0DrainInput


/-- The entire existing P(z)+S0-drain+Q(z) source composition can be
started from the root's *side-based* first q4 checkpoint after the
parameter reindexing.  The remaining actual-run boundary is the
pointwise equality between firstQ4Checkpoint_run's q4FrameAt output
and firstQ4P1Tape. -/
theorem firstQ4P1_sideCycle_to_secondFrame
    (L A z : Nat) (hA : 0 < A) (hz : 1 ≤ z) :
    run tm2
      ((3*2^z+3*z+58) +
        ((6*4^(2^z-1)+42*2^(2^z-1)-12*(2^z-1)-48) +
          (9*2^z+9*z+16)))
      ⟨4,1,firstQ4P1Tape L A z⟩ =
    some (frameAt
      (sweptLeft (3*(2^z-1)+3*z+7)
        (firstCycleS0DrainOutput z
          (List.replicate 4 true ++
            binDec (firstQ4P1Width L A) (firstQ4P1Value L A) ++ lh)).tape
        (3*2^z+3*z+7))
      3 firstCyclePostludeInside firstCyclePostludeEnd) := by
  rw [firstQ4P1Tape_eq_firstCycleCheckpointTape L A z hA]
  exact positiveZFirstCycle_from_checkpoint z
    (firstQ4P1Width L A) (firstQ4P1Value L A)
    hz (firstQ4P1Value_lt L A hA)

#print axioms firstQ4P1_sideCycle_to_secondFrame

end BB6Coverage.Agent42FirstQ4P1Reparam

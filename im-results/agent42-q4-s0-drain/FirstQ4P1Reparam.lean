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

end BB6Coverage.Agent42FirstQ4P1Reparam

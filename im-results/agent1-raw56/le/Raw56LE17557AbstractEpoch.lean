import Raw56LE17557FrameMachine
import Raw56LE17557RightLevel

namespace BB6.Agent1Raw56.LE17557AbstractEpoch
open BB6.Agent1Raw56.LE17557FrameMachine
open BB6.Agent1Raw56.LE17557RightLevel

/-- The two now-proved algebraic halves of physical epoch k (C_(k+2) to
    C_(k+3)): the complete rank-labelled action word exactly consumes the
    checkpoint-scale root runway, and the fixed right-level map exactly
    advances the dyadic checkpoint vector.  The remaining theorem is the
    source semantic synchronization identifying the actual triad orbit with
    this abstract epoch. -/
theorem abstract_epoch_checkpoint (k : Nat) :
    execLow (actionEpoch k) [2^(k+4)] = some [] ∧
    level (checkpointRight (k+2)) = checkpointRight (k+3) := by
  constructor
  · simpa using actionEpoch_consumes_root k []
  · have hk : 2 ≤ k+2 := by omega
    have hr := level_checkpointRight (k+2) hk
    simpa [Nat.add_assoc] using hr

#print axioms abstract_epoch_checkpoint

end BB6.Agent1Raw56.LE17557AbstractEpoch

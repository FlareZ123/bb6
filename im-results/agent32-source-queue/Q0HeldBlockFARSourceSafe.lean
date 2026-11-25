import SourceQueueBlockFARBridge
import Q00300SourceConsumer
import Q0400BSourceConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Q0HeldSourceSafe

open BB6Coverage
open BB6.Agent5Enumerate62
open BB6.Agent32SourceQueue
open BB6.Agent32SourceBlockFAR

/-- The exact q0 offset-300 table, represented as a SourceNode. The
    reachability metadata is irrelevant to SourceSafe; the theorem is
    completion-universal. -/
def q00300Node : SourceNode :=
  { tm := sourceTMOfBlockFAR BB6Generated.Q00300.literal
    holes := [((4 : Fin 6), true)]
    fresh := 6 }

/-- The exact q0 offset-400b table, represented as a SourceNode. -/
def q0400BNode : SourceNode :=
  { tm := sourceTMOfBlockFAR BB6Generated.Q0400B.literal
    holes := [((4 : Fin 6), false)]
    fresh := 6 }

theorem q00300_sourceSafe (B : Nat) : SourceSafe B q00300Node := by
  apply sourceSafe_of_blockFAR_table B q00300Node BB6Generated.Q00300.literal
  · simpa [q00300Node] using
      (sourcePartial_sourceTMOfBlockFAR BB6Generated.Q00300.literal).symm
  · intro m hm
    exact BB6Generated.Q00300.source_never m
      (by simpa [BB6Generated.Q00300.sourceTable] using hm)

theorem q0400B_sourceSafe (B : Nat) : SourceSafe B q0400BNode := by
  apply sourceSafe_of_blockFAR_table B q0400BNode BB6Generated.Q0400B.literal
  · simpa [q0400BNode] using
      (sourcePartial_sourceTMOfBlockFAR BB6Generated.Q0400B.literal).symm
  · intro m hm
    exact BB6Generated.Q0400B.source_never m
      (by simpa [BB6Generated.Q0400B.sourceTable] using hm)

#print axioms q00300_sourceSafe
#print axioms q0400B_sourceSafe

end BB6.Agent32Q0HeldSourceSafe

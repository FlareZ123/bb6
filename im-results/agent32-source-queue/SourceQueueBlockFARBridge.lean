import SourceQueueImplication
import BlockFARBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32SourceBlockFAR

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent5Enumerate62
open BB6.Agent32SourceQueue

/-- Convert the exact Enumerate62 source-node table into the table format
    consumed by the independent BlockFAR checker. -/
def sourceTable (tm : SourceTM) : BB6BlockFAR.Table :=
  fun q b => (tm (q,b)).map fun mv => ⟨mv.write, mv.right, mv.next⟩

/-- The conversion preserves the original partial-machine semantics
    definitionally, including genuinely unassigned transition slots. -/
theorem partialTable_sourceTable (tm : SourceTM) :
    BB6BlockFAR.partialTable (sourceTable tm) = sourcePartial tm := by
  funext s
  rcases s with ⟨q,b⟩
  cases h : tm (q,b) <;> rfl

/-- Any valid BlockFAR certificate for a source node immediately discharges
    its SourceSafe obligation for every compatible total completion. -/
theorem sourceSafe_of_blockFAR {d n} (B : Nat) (x : SourceNode)
    (C : BB6BlockFAR.Data d n)
    (hC : C.Valid (sourceTable x.tm)) :
    SourceSafe B x := by
  intro _ m hm
  have hm' : BB6Coverage.compatible
      (BB6BlockFAR.partialTable (sourceTable x.tm)) m := by
    simpa [partialTable_sourceTable] using hm
  exact BB6.Agent13BlankDelay.weighted_of_never B m
    (BB6BlockFAR.Data.source_never C (sourceTable x.tm) hC m hm')

#print axioms partialTable_sourceTable
#print axioms sourceSafe_of_blockFAR

end BB6.Agent32SourceBlockFAR

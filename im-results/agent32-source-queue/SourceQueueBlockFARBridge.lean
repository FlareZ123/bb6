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

/-- A nonhalting proof for every compatible completion is already
    exactly the semantic content needed by SourceSafe. -/
theorem sourceSafe_of_never (B : Nat) (x : SourceNode)
    (hNever : ∀ m, BB6Coverage.compatible (sourcePartial x.tm) m →
      BB6Coverage.NeverHalts m) : SourceSafe B x := by
  intro _ m hm
  exact BB6.Agent13BlankDelay.weighted_of_never B m (hNever m hm)

/-- Transport a BlockFAR completion theorem to the exact SourceTM node
    whenever the two partial-machine representations agree. -/
theorem sourceSafe_of_blockFAR_table (B : Nat) (x : SourceNode)
    (M : BB6BlockFAR.Table)
    (hEq : BB6BlockFAR.partialTable M = sourcePartial x.tm)
    (hNever : ∀ m, BB6Coverage.compatible (BB6BlockFAR.partialTable M) m →
      BB6Coverage.NeverHalts m) : SourceSafe B x := by
  apply sourceSafe_of_never B x
  intro m hm
  exact hNever m (by simpa [hEq] using hm)

/-- Any valid BlockFAR certificate for a source node immediately discharges
    its SourceSafe obligation for every compatible total completion. -/
theorem sourceSafe_of_blockFAR {d n} (B : Nat) (x : SourceNode)
    (C : BB6BlockFAR.Data d n)
    (hC : C.Valid (sourceTable x.tm)) :
    SourceSafe B x := by
  apply sourceSafe_of_blockFAR_table B x (sourceTable x.tm)
    (partialTable_sourceTable x.tm)
  intro m hm
  exact BB6BlockFAR.Data.source_never C (sourceTable x.tm) hC m hm

#print axioms partialTable_sourceTable
#print axioms sourceSafe_of_blockFAR

end BB6.Agent32SourceBlockFAR

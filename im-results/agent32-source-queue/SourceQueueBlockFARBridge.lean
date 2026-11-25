import SourceQueueImplication
import BlockFARBridge
import WeightedFirstOneCover

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
  cases h : tm (q,b) with
  | none =>
      simp [BB6BlockFAR.partialTable, sourceTable, sourcePartial, h]
  | some mv =>
      cases mv
      simp [BB6BlockFAR.partialTable, sourceTable, sourcePartial,
        BB6BlockFAR.sourceMove, h]

/-- Read a BlockFAR table back into the exact Enumerate62 SourceTM
    representation. -/
def sourceTMOfBlockFAR (M : BB6BlockFAR.Table) : SourceTM :=
  fun s => (M s.1 s.2).map BB6BlockFAR.sourceMove

theorem sourcePartial_sourceTMOfBlockFAR (M : BB6BlockFAR.Table) :
    sourcePartial (sourceTMOfBlockFAR M) = BB6BlockFAR.partialTable M := by
  funext s
  rcases s with ⟨q,b⟩
  cases h : M q b with
  | none =>
      simp [sourcePartial, sourceTMOfBlockFAR, BB6BlockFAR.partialTable, h]
  | some mv =>
      cases mv
      simp [sourcePartial, sourceTMOfBlockFAR, BB6BlockFAR.partialTable,
        BB6BlockFAR.sourceMove, h]

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

/-- A BlockFAR `Data.Valid` certificate and an explicit equality of
    partial-machine representations discharge the exact source-node
    `SourceSafe` obligation. -/
theorem sourceSafe_of_blockFAR_certificate {d n} (B : Nat) (x : SourceNode)
    (M : BB6BlockFAR.Table) (C : BB6BlockFAR.Data d n)
    (hC : C.Valid M)
    (hEq : BB6BlockFAR.partialTable M = sourcePartial x.tm) :
    SourceSafe B x := by
  apply sourceSafe_of_blockFAR_table B x M hEq
  intro m hm
  exact BB6BlockFAR.Data.source_never C M hC m hm

/-- If a source node is literally the SourceTM view of a BlockFAR table,
    the equality premise is automatic. -/
theorem sourceSafe_of_blockFAR_sourceTM {d n} (B : Nat) (x : SourceNode)
    (M : BB6BlockFAR.Table) (C : BB6BlockFAR.Data d n)
    (hC : C.Valid M)
    (hTM : x.tm = sourceTMOfBlockFAR M) :
    SourceSafe B x := by
  apply sourceSafe_of_blockFAR_certificate B x M C hC
  rw [hTM, sourcePartial_sourceTMOfBlockFAR]

/-- Any valid BlockFAR certificate for the table reconstructed from a
    source node immediately discharges its SourceSafe obligation. -/
theorem sourceSafe_of_blockFAR {d n} (B : Nat) (x : SourceNode)
    (C : BB6BlockFAR.Data d n)
    (hC : C.Valid (sourceTable x.tm)) :
    SourceSafe B x := by
  apply sourceSafe_of_blockFAR_certificate B x (sourceTable x.tm) C hC
  exact partialTable_sourceTable x.tm

#print axioms partialTable_sourceTable
#print axioms sourcePartial_sourceTMOfBlockFAR
#print axioms sourceSafe_of_never
#print axioms sourceSafe_of_blockFAR_table
#print axioms sourceSafe_of_blockFAR_certificate
#print axioms sourceSafe_of_blockFAR_sourceTM
#print axioms sourceSafe_of_blockFAR

end BB6.Agent32SourceBlockFAR

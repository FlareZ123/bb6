import FourHoleResidualRoster
import ExceptionalCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13RosterConvergence

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50RecursiveResidual

/-- The Agent31 frontier, losslessly packed into the common twelve-slot
    representation used by the Agent50 recursive certificate. -/
def agent31PackedRoster : List PackedTable :=
  remainingRootRoster.map fun e => packTable e.2

/-- The two independently constructed residual frontiers are exactly the
    same finite set of partial transition tables.  This is checked by kernel
    computation over all twelve slots, not by hashes or cardinalities. -/
theorem agent31PackedRoster_perm_closedRootRoster :
    List.Perm agent31PackedRoster closedRootRoster := by
  decide

/-- Transfer the sharper 395 weighted bound from the seven-edge proof to
    the canonical Agent50 roster.  The roster equality is the only bridge:
    no residual table is dropped or weakened. -/
theorem closedRootRoster_sound_395 :
    ∀ m, compatible root m → WeightedBound 395 m ∨
      ∃ q ∈ closedRootRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases remainingRootRoster_sound m hm with hbound | ⟨e, he, hc⟩
  · exact Or.inl hbound
  · have hpack : packTable e.2 ∈ agent31PackedRoster := by
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hclosed : packTable e.2 ∈ closedRootRoster :=
      (List.Perm.mem_iff agent31PackedRoster_perm_closedRootRoster).mp hpack
    exact Or.inr ⟨packTable e.2, hclosed, by
      simpa only [unpack_packTable] using hc⟩

#print axioms agent31PackedRoster_perm_closedRootRoster
#print axioms closedRootRoster_sound_395

end BB6.Agent13RosterConvergence

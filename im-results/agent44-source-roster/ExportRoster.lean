import SourceRosterEncoding

namespace BB6.Agent44SourceRoster

open BB6.Agent50RootFrontier
open BB6.Agent13RosterConvergence

/-- Canonical twelve-slot strings for the exact 124-table residual frontier.
    On this roster no entry uses the RootFrontier-only "HALT" marker, so the
    strings are directly consumable by the pinned BusyCoq TM_from_str parser. -/
def canonicalResidualRosterStrings : List String :=
  canonicalResidualRoster.map fun t =>
    BB6.Agent50RootFrontier.encodeTable (unpackTable t)

theorem canonicalResidualRosterStrings_count :
    canonicalResidualRosterStrings.length = 124 := by
  simpa [canonicalResidualRosterStrings] using canonicalResidualRoster_count

#eval canonicalResidualRosterStrings

end BB6.Agent44SourceRoster

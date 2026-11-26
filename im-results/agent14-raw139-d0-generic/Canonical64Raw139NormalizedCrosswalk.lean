import Canonical64Raw139Subcover
import Raw139E0ZeroRAIntegrated

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical64Raw139Crosswalk

open BB6Coverage
open BB6.Agent31FourHoleRoster
open BB6.Agent6Raw139Normalized
open BB6.Agent3Raw139E0ZeroRAIntegrated
open BB6.Agent14Canonical64Raw139Subcover

/-- True when every fixed transition of p is also fixed identically by q.
    Thus every completion of q is a completion of p, and a Cover of p
    transports to q. -/
def extendsTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all (fun s =>
    [false, true].all (fun b =>
      match p (s, b) with
      | none => true
      | some v => q (s, b) == some v))

/-- The active Canonical64 Raw139 leaves after the accepted 0RA Cover. -/
def activeRows := remainingRaw139AfterFortyThreeWithoutE0

/-- The 66 unresolved normalized Raw139 tables after the accepted 0RA Cover. -/
def normalizedTables := remainingTablesAfter

def activeCoveredByNormalized : List (List Move × PartialMachine) :=
  activeRows.filter (fun e =>
    normalizedTables.any (fun p => extendsTable p e.2))

def activeUncoveredByNormalized : List (List Move × PartialMachine) :=
  activeRows.filter (fun e =>
    !(normalizedTables.any (fun p => extendsTable p e.2)))

def activeCoverageCounts : List Nat :=
  normalizedTables.map (fun p =>
    (activeRows.filter (fun e => extendsTable p e.2)).length)

def e0LCTable : PartialMachine := leaf (2, ⟨false, false, 2⟩)

/-- Finite crosswalk diagnostics. The first count is how many active leaves
    are refinements of at least one normalized residual table; the second is
    how many are not. The final counts test E0=0LC by exact equality and by
    the more useful refinement relation. -/
#eval (normalizedTables.length, activeRows.length,
  activeCoveredByNormalized.length, activeUncoveredByNormalized.length)
#eval activeCoverageCounts
#eval (activeRows.filter (fun e => sameTable e.2 e0LCTable)).length
#eval (activeRows.filter (fun e => extendsTable e0LCTable e.2)).length

end BB6.Agent14Canonical64Raw139Crosswalk

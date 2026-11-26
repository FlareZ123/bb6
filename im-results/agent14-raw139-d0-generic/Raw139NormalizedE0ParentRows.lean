import Raw139E0ZeroRAIntegrated

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0ParentRows

open BB6Coverage
open BB6.Agent6Raw139Normalized
open BB6.Agent3Raw139E0ZeroRAIntegrated

/-- The normalized E0=0RE parent table. -/
def e0RETable : PartialMachine := leaf (2, ⟨false, true, 4⟩)

/-- The normalized E0=0RB parent table. -/
def e0RBTable : PartialMachine := leaf (2, ⟨false, true, 1⟩)

/-- The normalized E0=0RD parent table. -/
def e0RDTable : PartialMachine := leaf (2, ⟨false, true, 3⟩)

/-- The 66 normalized Raw139 residual tables after the source-accepted E0=0RA
    parent has been removed. -/
def normalizedTables : List PartialMachine := remainingTablesAfter

theorem e0RE_occurs_once :
    (normalizedTables.filter (fun p => sameTable p e0RETable)).length = 1 := by
  decide

theorem e0RB_occurs_once :
    (normalizedTables.filter (fun p => sameTable p e0RBTable)).length = 1 := by
  decide

theorem e0RD_occurs_once :
    (normalizedTables.filter (fun p => sameTable p e0RDTable)).length = 1 := by
  decide

/-- Removing the three distinct E0 parent rows leaves exactly 63 normalized
    residual tables. The Covers for E0=0RE/0RB/0RD are separate premises and
    are not asserted by this finite membership module. -/
def normalizedTablesWithoutE0RE0RB0RD : List PartialMachine :=
  normalizedTables.filter (fun p =>
    !(sameTable p e0RETable) && !(sameTable p e0RBTable) &&
    !(sameTable p e0RDTable))

theorem normalizedTablesWithoutE0RE0RB0RD_count :
    normalizedTablesWithoutE0RE0RB0RD.length = 63 := by
  decide

#print axioms e0RE_occurs_once
#print axioms e0RB_occurs_once
#print axioms e0RD_occurs_once
#print axioms normalizedTablesWithoutE0RE0RB0RD_count

end BB6.Agent14Raw139NormalizedE0ParentRows

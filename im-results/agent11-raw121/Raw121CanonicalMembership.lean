import Canonical78Roster
import ThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw121CanonicalMembership

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster

/-- Raw121 is the off-path E1=1RE sibling of the first-one route. -/
def parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4, true)
    (some ⟨true, true, 4⟩)

/-- Match the exact finite 12-slot table, not a hash or an enumeration index. -/
def inCanonical78 : Bool :=
  BB6.Agent47Canonical78.roster.any fun e => sameTable e.2 parent

theorem inCanonical78_checked : inCanonical78 = true := by
  decide

/-- The six-hole raw121 cylinder is one of the 78 canonical residuals. -/
theorem parent_mem :
    ∃ e ∈ BB6.Agent47Canonical78.roster, e.2 = parent := by
  obtain ⟨e, he, htable⟩ := List.any_eq_true.mp inCanonical78_checked
  exact ⟨e, he, sameTable_sound htable⟩

/-- The path-derived parent has exactly the raw121 transition assignments. -/
theorem parent_shape :
    parent (0, false) = some (some ⟨true, true, 1⟩) ∧
    parent (1, false) = some (some ⟨true, true, 2⟩) ∧
    parent (2, false) = some (some ⟨false, true, 3⟩) ∧
    parent (3, false) = some (some ⟨true, false, 3⟩) ∧
    parent (3, true) = some (some ⟨true, true, 4⟩) ∧
    parent (4, true) = some (some ⟨true, true, 4⟩) ∧
    parent (0, true) = none ∧
    parent (1, true) = none ∧
    parent (2, true) = none ∧
    parent (4, false) = none ∧
    parent (5, false) = none ∧
    parent (5, true) = none := by
  decide

#print axioms inCanonical78_checked
#print axioms parent_mem
#print axioms parent_shape

end BB6.Agent11Raw121CanonicalMembership

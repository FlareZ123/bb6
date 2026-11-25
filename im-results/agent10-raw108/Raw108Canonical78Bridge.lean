import Canonical78Roster
import Raw108RootCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10Raw108Canonical78

open BB6.Agent47CanonicalFrontier
open BB6.Agent47Canonical78
open BB6.Agent10Raw108Root

/-- The raw108 parent is canonical residual index 73 (raw residual index
    108): B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=1LB. -/
theorem parent_in_canonical_remaining :
    ∃ e ∈ canonicalRemainingRoster, e.2 = parent := by
  decide

/-- The exact raw108 table is not one of the eighteen already-removed
    early-bound cylinders. -/
theorem parent_not_covered :
    BB6.Agent47Combined106.covered parent = false := by
  decide

/-- Thus raw108 is an actual member of the 78 quotient-compatible
    residual representatives, not merely a related raw-labelled table. -/
theorem parent_in_roster :
    ∃ e ∈ roster, e.2 = parent := by
  rcases parent_in_canonical_remaining with ⟨e, he, hEq⟩
  have hcovered : BB6.Agent47Combined106.covered e.2 = false := by
    simpa [hEq] using parent_not_covered
  have hfilter : !(BB6.Agent47Combined106.covered e.2) = true := by
    simp [hcovered]
  exact ⟨e, List.mem_filter.mpr ⟨he, hfilter⟩, hEq⟩

#print axioms parent_in_canonical_remaining
#print axioms parent_not_covered
#print axioms parent_in_roster

end BB6.Agent10Raw108Canonical78

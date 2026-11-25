import Raw118Base
import Canonical78Roster

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118

open BB6Coverage BB6.Agent47Canonical78

/-- The five authentic first-hole assignments locating Raw118 inside the
    canonical first-one residual frontier. -/
def parentAddress : List Move :=
  [⟨true, true, 2⟩, ⟨false, true, 3⟩, ⟨true, false, 3⟩,
   ⟨true, true, 4⟩, ⟨false, false, 4⟩]

/-- Raw118 is not an unrelated side experiment: its exact six-hole parent is
    the canonical residual at address 1RC,0RD,1LD,1RE,0LE. -/
theorem parent_mem_canonical78 :
    (parentAddress, parent) ∈ BB6.Agent47Canonical78.roster := by
  decide

#print axioms parent_mem_canonical78

end BB6.Agent16Raw118

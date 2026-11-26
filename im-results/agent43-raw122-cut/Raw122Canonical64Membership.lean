import Canonical64Raw120Integrated
import Raw122Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent43Raw122Canonical64Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent31Canonical65AfterThree

/-- The exact Raw122 six-hole parent represented in the Canonical64 quotient. -/
abbrev p122 : PartialMachine := BB6.Agent43Raw122.parent

theorem p122_root :
    p122 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent43Raw122.parent_root

/-- Exact, unique sameTable membership in the accepted Canonical64 roster.
    This is a membership certificate only; it does not claim the Raw122 Cover
    has passed or alter the accepted Canonical64 roster. -/
theorem p122_parent_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p122)).length = 1 := by
  decide

#eval BB6.Agent3Canonical64Raw120.roster64.findIdx
  (fun e => sameTable e.2 p122)

#print axioms p122_root
#print axioms p122_parent_count64

end BB6.Agent43Raw122Canonical64Membership

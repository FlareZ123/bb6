import Canonical58Raw113Graft
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical58Raw83Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical58Raw113Graft

/-- Raw83's exact four-hole parent, matching the source-accepted table
    1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA. -/
abbrev p83 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p83_count58 :
    (BB6.Agent31Canonical58Raw113Graft.roster58.filter
      (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem p83_distinct_from_p113 :
    ∀ p ∈ [p113], sameTable p p83 = false := by decide

#print axioms p83_root
#print axioms p83_count58
#print axioms p83_distinct_from_p113

end BB6.Agent31Canonical58Raw83Membership

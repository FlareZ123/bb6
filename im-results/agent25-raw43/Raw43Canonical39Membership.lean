import Raw39Canonical39Successor
import Raw43Canonical40Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact membership of Raw43 in the source-accepted Canonical39 successor produced
by removing Raw39 from Canonical40. This is the cumulative lineage needed for a
future 39 -> 38 reduction.
-/

namespace BB6.Agent25Raw43Canonical39Membership

open BB6Coverage BB6.Agent31FourHoleRoster

abbrev p : PartialMachine := BB6.Agent25Raw43Canonical40Membership.p
noncomputable abbrev roster39 :=
  BB6.Agent11Raw39Canonical39Successor.roster39

theorem parent_present :
    (roster39.filter (fun e => sameTable e.2 p)).length = 1 := by decide

#print axioms parent_present

end BB6.Agent25Raw43Canonical39Membership

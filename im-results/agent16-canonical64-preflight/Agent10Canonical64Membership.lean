import Canonical64Raw120Integrated
import Raw106Data
import Raw79Data
import Raw67Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent31Canonical65AfterThree

namespace BB6.Agent16Agent10Canonical64Membership

abbrev p106 : PartialMachine := BB6.Agent10Raw106.p106
abbrev p79 : PartialMachine := BB6.Agent10Raw79.p79
abbrev p67 : PartialMachine := BB6.Agent10Raw67.p67

theorem p106_root : p106 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw106.p106_root
theorem p79_root : p79 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw79.p79_root
theorem p67_root : p67 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw67.p67_root

theorem p106_parent_count64 :
    (roster64.filter (fun e => sameTable e.2 p106)).length = 1 := by decide
theorem p79_parent_count64 :
    (roster64.filter (fun e => sameTable e.2 p79)).length = 1 := by decide
theorem p67_parent_count64 :
    (roster64.filter (fun e => sameTable e.2 p67)).length = 1 := by decide

theorem p106_p79_distinct : sameTable p106 p79 = false := by decide
theorem p106_p67_distinct : sameTable p106 p67 = false := by decide
theorem p79_p67_distinct : sameTable p79 p67 = false := by decide

#print axioms p106_root
#print axioms p79_root
#print axioms p67_root
#print axioms p106_parent_count64
#print axioms p79_parent_count64
#print axioms p67_parent_count64
#print axioms p106_p79_distinct
#print axioms p106_p67_distinct
#print axioms p79_p67_distinct

end BB6.Agent16Agent10Canonical64Membership

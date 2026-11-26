import Canonical58Raw113Graft
import Raw57ParentBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Canonical58Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical58Raw113Graft

/-- The exact six-hole Raw57 parent from the historical Canonical64 address;
    membership is checked against the accepted Canonical58 roster itself. -/
abbrev p57 : PartialMachine := BB6.Agent1Raw57Parent.parent

/-- Raw57 has the blank-start root required by the canonical parent interface. -/
theorem p57_root :
    p57 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Exact unique table membership in the accepted 58-entry roster. -/
theorem p57_count58 :
    (BB6.Agent31Canonical58Raw113Graft.roster58.filter
      (fun e => sameTable e.2 p57)).length = 1 := by
  decide

/-- Raw57 is not the already-consumed Raw113 parent. -/
theorem p57_distinct_from_p113 :
    ∀ p ∈ [BB6.Agent31Canonical59Raw113Membership.p113],
      sameTable p p57 = false := by
  decide

/-- The exact complement after removing Raw57 has 57 entries. -/
noncomputable def roster57 : List (Nat × PartialMachine) :=
  removeParents [p57] BB6.Agent31Canonical58Raw113Graft.roster58

theorem count57 : roster57.length = 57 := by
  decide

/-- Raw59 remains in the complement after the Raw57 membership cut. -/
theorem raw59_retained :
    (roster57.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = 1 := by
  decide

/-- Raw113 is absent because it was consumed in the accepted Canonical58 graft. -/
theorem raw113_absent :
    (roster57.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by
  decide

#print axioms p57_root
#print axioms p57_count58
#print axioms p57_distinct_from_p113
#print axioms count57
#print axioms raw59_retained
#print axioms raw113_absent

end BB6.Agent1Raw57Canonical58Membership

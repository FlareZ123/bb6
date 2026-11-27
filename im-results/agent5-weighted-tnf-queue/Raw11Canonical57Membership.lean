import Raw124Canonical58Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5Raw11Canonical57Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47PhaseFrontier BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch

/-- Canonical raw residual 11: the B0=1RC, C0=0LA branch from the first-one root.
    This is exactly the parent table exported as q32Parent by Agent24. -/
def p11 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | _, _ => none

theorem p11_encoding :
    encodeTable p11 =
      "1RB---_1RC---_0LA---_------_------_------" := by
  decide

/-- Raw11 is a unique member of the source-accepted Canonical58 roster
    after the accepted Raw113 delta. -/
theorem p11_count58 :
    (BB6.Agent31Canonical58Raw113Graft.roster58.filter
      (fun e => sameTable e.2 p11)).length = 1 := by
  decide

/-- Raw11 remains a unique member of the actual Canonical57 successor
    after the accepted Raw124 parent Cover is consumed. -/
theorem p11_count57 :
    (BB6.Agent2Raw124Canonical58Membership.roster57.filter
      (fun e => sameTable e.2 p11)).length = 1 := by
  decide

theorem p11_distinct_from_raw124 :
    sameTable p11 BB6.Agent2Raw124Canonical58Membership.p124 = false := by
  decide

theorem p11_root :
    p11 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

#print axioms p11_encoding
#print axioms p11_count58
#print axioms p11_count57
#print axioms p11_distinct_from_raw124
#print axioms p11_root

end BB6.Agent5Raw11Canonical57Membership

import Canonical40Extra57

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact-source membership preflight for the seven-hole Raw42 parent.
This only proves literal membership in the accepted Canonical40 roster; it does
not assert a parent Cover or a global reduction.
-/

namespace BB6.Agent17Raw42Canonical40Membership
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster

/-- Raw42 parent: 1RB---_1RC---_0RD---_1LD0LB_------_------. -/
def p : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_present :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 := by decide

#print axioms parent_present
end BB6.Agent17Raw42Canonical40Membership

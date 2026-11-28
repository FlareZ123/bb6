import Canonical40Extra57

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact-source Canonical40 membership preflight for the literal Raw54 parent.
The reconstructed raw-index JSON is discovery evidence only; this declaration
is intended to be compiled against the accepted Canonical40Extra57 closure.
-/

namespace BB6.Agent8Raw54Canonical40Membership
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster

/-- Literal Raw54: 1RB---_1RC---_0RD---_1LD0LE_------_------. -/
def p : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem parent_present :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 := by decide

theorem parent_root :
    p initialSlot = some (some ⟨true,true,1⟩) := by decide

#print axioms parent_present
#print axioms parent_root
end BB6.Agent8Raw54Canonical40Membership

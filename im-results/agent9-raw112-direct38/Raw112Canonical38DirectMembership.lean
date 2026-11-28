import Canonical38Raw39Raw47Direct

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Literal Raw112 membership preflight on the accepted direct Raw39+Raw47
Canonical38 lineage.  This file deliberately does not import the heavyweight
Raw112 whole-parent proof, so roster membership can be source-checked
independently of the parent assembly.
-/

namespace BB6.Agent9Raw112Canonical38DirectMembership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster

/-- Raw112 parent: 1RB---_1RC---_0RD---_1LD1RE_---1LC_------. -/
def p112 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,true  => some (some ⟨true,false,2⟩)
  | _,_ => none

noncomputable abbrev baseRoster :=
  BB6.Agent3Canonical38Raw39Raw47Direct.roster38

theorem parent_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem parent_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

#print axioms parent_count38
#print axioms parent_root

end BB6.Agent9Raw112Canonical38DirectMembership

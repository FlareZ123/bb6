import Canonical40Extra57

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Proposed exact-source membership preflight. Does not use a reconstructed
40-item manifest as a substitute for the accepted Lean roster.
Requires the accepted Canonical40Extra57 source/object closure before this
module can be compiled. The theorem is *unaccepted* until that check passes.
-/

namespace BB6.Agent11Raw39Canonical40Membership
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster

/-- The literal Raw39 first-hole cylinder: 1RB---_1RC---_0RD---_1LD0RA_------_------. -/
def p : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,0⟩)
  | _,_ => none

/-- The accepted Canonical40 quotient frontier contains this exact physical parent once. -/
theorem parent_present :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 := by decide

/-- Raw39 is not the already certified Raw47 parent (different D1 action). -/
def p47 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,2⟩)
  | _,_ => none

theorem distinct_from_raw47 : sameTable p p47 = false := by decide

#print axioms parent_present
#print axioms distinct_from_raw47

end BB6.Agent11Raw39Canonical40Membership

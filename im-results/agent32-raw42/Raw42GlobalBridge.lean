import Raw42NamedJoin

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw42GlobalBridge
open BB6Coverage BB6.Agent50TNFPilot
open BB6.Agent32Raw42
open BB6.Agent32Raw42NamedJoin

/-- Raw42's exact literal seven-hole parent, kept local so the local join can
    be checked without reconstructing the generated global roster source. -/
def literal : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_eq_literal : parent = literal := by
  apply tableOK_sound
  decide

/-- The exact mix of already-used Raw42 child bounds is sufficient for the
    fixed global threshold.  Only 0RA and 0RB need lifting from 1006 to 100006;
    the other ten children are consumed at the assembly bound 100006. -/
theorem global_cover_from_named
    (h0LA : Cover (WeightedBound 100006) (child ⟨false,false,0⟩))
    (h0RA : Cover (WeightedBound 1006)   (child ⟨false,true,0⟩))
    (h1LA : Cover (WeightedBound 100006) (child ⟨true,false,0⟩))
    (h1RA : Cover (WeightedBound 100006) (child ⟨true,true,0⟩))
    (h0RB : Cover (WeightedBound 1006)   (child ⟨false,true,1⟩))
    (h1LB : Cover (WeightedBound 100006) (child ⟨true,false,1⟩))
    (h1RB : Cover (WeightedBound 100006) (child ⟨true,true,1⟩))
    (h1LC : Cover (WeightedBound 100006) (child ⟨true,false,2⟩))
    (h0LE : Cover (WeightedBound 100006) (child ⟨false,false,4⟩))
    (h0RE : Cover (WeightedBound 100006) (child ⟨false,true,4⟩))
    (h1LE : Cover (WeightedBound 100006) (child ⟨true,false,4⟩))
    (h1RE : Cover (WeightedBound 100006) (child ⟨true,true,4⟩)) :
    Cover (WeightedBound 6766859) literal := by
  have hp : Cover (WeightedBound 100006) parent :=
    cover_from_named 100006 (by decide)
      h0LA (lift_cover (by decide) h0RA) h1LA h1RA
      (lift_cover (by decide) h0RB) h1LB h1RB h1LC
      h0LE h0RE h1LE h1RE
  rw [← parent_eq_literal]
  exact lift_cover (by decide) hp

#print axioms parent_eq_literal
#print axioms global_cover_from_named
end BB6.Agent17Raw42GlobalBridge

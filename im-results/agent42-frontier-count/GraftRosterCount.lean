import CanonicalRosterRefinement

namespace BB6.Agent42FrontierCount

open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement

abbrev Entry := List Move × PartialMachine

/-- Count the exact parents selected by the table-equality graft. -/
def graftMatchCount (p : PartialMachine) (roster : List Entry) : Nat :=
  (roster.filter (fun e => sameTable e.2 p)).length

/-- Structural length accounting for graftRoster. The additive form avoids
    nonlinear Nat subtraction and is stable under large function-valued
    rosters. -/
theorem graftRoster_length_add_count (p : PartialMachine)
    (replacement roster : List Entry) :
    (graftRoster p replacement roster).length +
        graftMatchCount p roster =
      roster.length + graftMatchCount p roster * replacement.length := by
  induction roster with
  | nil =>
      simp [graftRoster,graftMatchCount]
  | cons e es ih =>
      by_cases h : sameTable e.2 p = true
      · simp [graftRoster,graftEntry,graftMatchCount,h,ih,
          Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [graftRoster,graftEntry,graftMatchCount,h,ih,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem graftRoster_length_of_one (p : PartialMachine)
    (replacement roster : List Entry)
    (hcount : graftMatchCount p roster = 1) :
    (graftRoster p replacement roster).length + 1 =
      roster.length + replacement.length := by
  simpa [graftMatchCount,hcount] using
    (graftRoster_length_add_count p replacement roster)

#print axioms graftRoster_length_add_count
#print axioms graftRoster_length_of_one

end BB6.Agent42FrontierCount

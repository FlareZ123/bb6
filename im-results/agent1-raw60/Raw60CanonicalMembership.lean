import Raw60RootCut
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw60CanonicalMembership

/-- The raw60 six-hole parent is an exact member of the current
    78-representative canonical quotient roster. -/
theorem parent_in_78 :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      e.2 = BB6.Agent1Raw60Root.parent := by
  have h : BB6.Agent47Canonical78.roster.any
      (fun e => BB6.Agent31ThreeHole.tableOK e.2 BB6.Agent1Raw60Root.parent) = true := by
    decide
  obtain ⟨e, he, hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e, he, BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩

/-- The parent retains the authentic first transition required by
    the quotient-roster graft theorem. -/
theorem parent_root_action :
    BB6.Agent1Raw60Root.parent initialSlot =
      some (some ⟨true, true, 1⟩) := by
  decide

#print axioms parent_in_78
#print axioms parent_root_action

end BB6.Agent1Raw60CanonicalMembership

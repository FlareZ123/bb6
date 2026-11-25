import Raw60RootCut
import CanonicalRaw114Accepted

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw60CanonicalMembership

/-- The six-hole raw60 parent still occurs as an exact cylinder in the
    currently accepted 77-representative quotient roster (after raw114). -/
theorem parent_in_77 :
    ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 = BB6.Agent1Raw60Root.parent := by
  have h : BB6.Agent47CanonicalRaw114Accepted.roster.any
      (fun e => BB6.Agent31ThreeHole.tableOK e.2 BB6.Agent1Raw60Root.parent) = true := by
    decide
  obtain ⟨e, he, hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e, he, BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩

/-- The parent retains the authentic first transition required by the
    quotient-roster graft theorem. -/
theorem parent_root_action :
    BB6.Agent1Raw60Root.parent initialSlot =
      some (some ⟨true, true, 1⟩) := by
  decide

#print axioms parent_in_77
#print axioms parent_root_action

end BB6.Agent1Raw60CanonicalMembership

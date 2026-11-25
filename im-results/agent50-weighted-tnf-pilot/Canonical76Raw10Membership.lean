import CanonicalTwoParentGraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Canonical76Raw10

open BB6Coverage
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalTwoParent

/-- The depth-one B0=1LC child of the authentic first-one cylinder. -/
abbrev raw10Parent : PartialMachine :=
  refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨true, false, ⟨2, by decide⟩⟩)

/-- B0=1LC remains an exact canonical residual after both accepted-parent
    grafts (raw107 and raw114). This is a finite table-membership check. -/
theorem raw10Parent_in_roster76 :
    ∃ e ∈ roster76, sameTable e.2 raw10Parent = true := by
  decide

/-- The roster contains the B0=1LC parent as an exact table, not merely as
    a compatible intersection. -/
theorem raw10Parent_exact_member :
    ∃ e ∈ roster76, e.2 = raw10Parent := by
  obtain ⟨e, he, hsame⟩ := raw10Parent_in_roster76
  exact ⟨e, he, sameTable_sound hsame⟩

/-- Exactly one of the 76 canonical obligations is the B0=1LC parent. -/
noncomputable def parentEntries :=
  roster76.filter fun e => sameTable e.2 raw10Parent

theorem parentEntries_count : parentEntries.length = 1 := by
  decide

/-- The other canonical obligations after isolating B0=1LC. -/
noncomputable def otherRoster :=
  roster76.filter fun e => !(sameTable e.2 raw10Parent)

theorem otherRoster_count : otherRoster.length = 75 := by
  decide

#print axioms raw10Parent_in_roster76
#print axioms raw10Parent_exact_member
#print axioms parentEntries_count
#print axioms otherRoster_count

end BB6.Agent50Canonical76Raw10

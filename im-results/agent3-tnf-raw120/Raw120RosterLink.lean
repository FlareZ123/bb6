import Combined109Roster
import Raw120Late

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120RosterLink

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent47Combined109
open BB6.Agent3Raw120

/-- The 85th entry of the exact 124-entry first-one residual list.
    Its canonical JSON address is canonical index 84 / raw index 120. -/
def raw120Entry : List Move × PartialMachine :=
  remainingRootRoster[84]'(by decide)

/-- The table at that exact residual address is definitionally the
    path-built raw120 parent used by the sibling certificate dossier. -/
theorem raw120_entry_matches :
    sameTable raw120Entry.2 p120 = true := by
  decide

theorem raw120_entry_table_eq : raw120Entry.2 = p120 :=
  sameTable_sound raw120_entry_matches

/-- The raw120 parent is not among the fifteen source-accepted residual
    cuts, so it remains in the 109-entry Combined109Roster. -/
theorem raw120_entry_not_covered : covered raw120Entry.2 = false := by
  rw [raw120_entry_table_eq]
  decide

theorem raw120_entry_in_reducedRoster : raw120Entry ∈ reducedRoster := by
  apply List.mem_filter.mpr
  refine ⟨List.getElem_mem (by decide), ?_⟩
  simp [raw120_entry_not_covered]

/-- Any completion of p120 is therefore still represented by one of the
    exact 109 residual cylinders; this identifies the local raw120 work
    with a concrete outstanding global maximality obligation. -/
theorem p120_compatible_in_109 (m : Machine) (hm : compatible p120 m) :
    ∃ e ∈ reducedRoster, compatible e.2 m := by
  refine ⟨raw120Entry, raw120_entry_in_reducedRoster, ?_⟩
  simpa [raw120_entry_table_eq] using hm

#print axioms raw120_entry_matches
#print axioms raw120_entry_in_reducedRoster
#print axioms p120_compatible_in_109

end BB6.Agent3Raw120RosterLink

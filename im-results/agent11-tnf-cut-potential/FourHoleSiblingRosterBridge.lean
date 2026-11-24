import FourHoleSiblingData
import ThreeHoleAudit
import FourHoleResidualRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11FourHoleSiblingBridge

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleSibling
open BB6.Agent31FourHoleRoster
open BB6.Agent31ThreeHole

/-- The F1=0RA four-hole sibling is one of the exact residual cylinders
    left by the 395-bound seven-edge first-one frontier. -/
theorem sibling_in_roster :
    ∃ e ∈ remainingRootRoster, e.2 = wideParent := by
  have h : remainingRootRoster.any (fun e => _root_.BB6.Agent31ThreeHole.tableOK e.2 wideParent) = true := by
    decide
  obtain ⟨e, he, hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e, he, _root_._root_.BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩

/-- Remove the now-certified sibling from the 124-cylinder residual roster. -/
def reducedRosterRA : List (List Move × PartialMachine) :=
  remainingRootRoster.filter fun e => !(_root_.BB6.Agent31ThreeHole.tableOK e.2 wideParent)

theorem reducedRosterRA_count : reducedRosterRA.length = 123 := by
  decide

/-- The sibling's 7014-bound certificate closes exactly one residual cylinder;
    all other residual cylinders remain explicit and unchanged. -/
theorem reducedRosterRA_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ reducedRosterRA, compatible e.2 m := by
  rcases remainingRootRoster_sound_7014 m hm with hbound | ⟨e, he, hp⟩
  · exact Or.inl hbound
  · by_cases hcheck : _root_.BB6.Agent31ThreeHole.tableOK e.2 wideParent = true
    · left
      have heq := _root_._root_.BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      exact all_completions_weighted m (heq ▸ hp)
    · right
      exact ⟨e, List.mem_filter.mpr ⟨he, by simpa using hcheck⟩, hp⟩

#print axioms sibling_in_roster
#print axioms reducedRosterRA_count
#print axioms reducedRosterRA_sound

end BB6.Agent11FourHoleSiblingBridge

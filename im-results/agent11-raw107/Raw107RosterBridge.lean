import Raw107ParentClosure
import FourHoleResidualRoster
import ThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw107RosterBridge

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster

/-- The raw107 six-hole parent is one exact member of the source-accepted
    124-cylinder first-one residual roster. -/
theorem raw107_in_roster :
    ∃ e ∈ remainingRootRoster, e.2 = BB6.Agent10Raw107Root.parent := by
  have h : remainingRootRoster.any
      (fun e => BB6.Agent31ThreeHole.tableOK e.2 BB6.Agent10Raw107Root.parent) = true := by
    decide
  obtain ⟨e, he, hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e, he, BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩

/-- Remove the completely bounded raw107 parent from the 124-entry roster. -/
noncomputable def reducedRoster : List (List Move × PartialMachine) :=
  remainingRootRoster.filter fun e =>
    !(BB6.Agent31ThreeHole.tableOK e.2 BB6.Agent10Raw107Root.parent)

theorem reduced_count : reducedRoster.length = 123 := by
  decide

/-- Every first-one-root completion is either bounded by 815 or belongs to
    one of the 123 exact residual cylinders remaining after raw107 closure. -/
theorem reduced_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 815 m ∨
      ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with hbound | ⟨e, he, hp⟩
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd) (by decide))
  · by_cases hcheck :
      BB6.Agent31ThreeHole.tableOK e.2 BB6.Agent10Raw107Root.parent = true
    · left
      have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      exact BB6.Agent11Raw107ParentClosure.all_completions m (heq ▸ hp)
    · right
      exact ⟨e, List.mem_filter.mpr ⟨he, by simpa using hcheck⟩, hp⟩

/-- The same reduced roster at the 7014 cutoff used by the combined global
    first-one dichotomy. -/
theorem reduced_sound_7014 (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases reduced_sound m hm with hbound | hres
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd) (by decide))
  · exact Or.inr hres

#print axioms raw107_in_roster
#print axioms reduced_count
#print axioms reduced_sound
#print axioms reduced_sound_7014

end BB6.Agent11Raw107RosterBridge

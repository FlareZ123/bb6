import Raw87Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw87
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
noncomputable def reducedRoster87 := remainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p87)
theorem raw87_in_roster : ∃ e ∈ remainingRootRoster, e.2 = p87 := by
  have h : remainingRootRoster.any (fun e => BB6.Agent31ThreeHole.tableOK e.2 p87) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩
theorem reduced87_count : reducedRoster87.length = 123 := by decide
theorem reduced87_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster87, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · by_cases hcheck : BB6.Agent31ThreeHole.tableOK e.2 p87 = true
    · left
      have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      have hbound := all87 m (heq ▸ hp)
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd) (by decide)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hcheck⟩,hp⟩
#print axioms raw87_in_roster
#print axioms reduced87_count
#print axioms reduced87_sound
end BB6.Agent10Raw87

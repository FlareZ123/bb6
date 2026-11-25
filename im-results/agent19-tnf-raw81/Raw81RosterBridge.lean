import Raw81Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw81
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster BB6.Agent10Raw81
noncomputable def reducedRoster81 := remainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p81)
theorem raw81_in_roster : ∃ e ∈ remainingRootRoster, e.2 = p81 := by
  have h : remainingRootRoster.any (fun e => BB6.Agent31ThreeHole.tableOK e.2 p81) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩
theorem reduced81_count : reducedRoster81.length = 123 := by decide
theorem reduced81_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ reducedRoster81, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl (by intro k d hk hd; exact Nat.le_trans (h k d hk hd) (by decide))
  · by_cases hcheck : BB6.Agent31ThreeHole.tableOK e.2 p81 = true
    · left
      have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      exact all81 m (heq ▸ hp)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hcheck⟩,hp⟩
#print axioms raw81_in_roster
#print axioms reduced81_count
#print axioms reduced81_sound
end BB6.Agent19Raw81

import Raw104Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw104
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
noncomputable def reducedRoster104 := remainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p104)
theorem raw104_in_roster : ∃ e ∈ remainingRootRoster, e.2 = p104 := by
  have h : remainingRootRoster.any (fun e => BB6.Agent31ThreeHole.tableOK e.2 p104) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩
theorem reduced104_count : reducedRoster104.length = 123 := by decide
theorem reduced104_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster104, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · by_cases hcheck : BB6.Agent31ThreeHole.tableOK e.2 p104 = true
    · left
      have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      have hbound := all104 m (heq ▸ hp)
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd) (by decide)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hcheck⟩,hp⟩
#print axioms raw104_in_roster
#print axioms reduced104_count
#print axioms reduced104_sound
end BB6.Agent8Raw104

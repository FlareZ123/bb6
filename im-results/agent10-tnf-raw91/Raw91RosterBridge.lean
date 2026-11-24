import Raw91Data
import PureFourHoleResiduals
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw91
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent44SourceRoster
def reducedRoster91 := pureRemainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p91)
theorem raw91_in_roster : ∃ e ∈ pureRemainingRootRoster, e.2 = p91 := by
  have h : pureRemainingRootRoster.any (fun e => BB6.Agent31ThreeHole.tableOK e.2 p91) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩
theorem reduced91_count : reducedRoster91.length = 123 := by decide
theorem reduced91_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster91, compatible e.2 m := by
  rcases pureRemainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · by_cases hcheck : BB6.Agent31ThreeHole.tableOK e.2 p91 = true
    · left
      have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      have hbound := all91 m (heq ▸ hp)
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd) (by decide)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hcheck⟩,hp⟩
#print axioms raw91_in_roster
#print axioms reduced91_count
#print axioms reduced91_sound
end BB6.Agent10Raw91

import Raw99Data
import PureFourHoleResiduals

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw99
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent44SourceRoster

def reducedRoster99 := pureRemainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p99)

theorem raw99_in_roster : ∃ e ∈ pureRemainingRootRoster, e.2 = p99 := by
  have h : pureRemainingRootRoster.any (fun e => BB6.Agent31ThreeHole.tableOK e.2 p99) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck⟩

theorem reduced99_count : reducedRoster99.length = 123 := by decide

theorem reduced99_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster99, compatible e.2 m := by
  rcases pureRemainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · by_cases hcheck : BB6.Agent31ThreeHole.tableOK e.2 p99 = true
    · left
      have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ hcheck
      have hbound := all99 m (heq ▸ hp)
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd) (by decide)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hcheck⟩,hp⟩

#print axioms reduced99_count
#print axioms reduced99_sound
end BB6.Agent2Raw99

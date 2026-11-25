import Raw115Data
import Raw119Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Six
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent8Raw115 BB6.Agent8Raw119
noncomputable def reducedRoster := remainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p115 || BB6.Agent31ThreeHole.tableOK e.2 p119)
theorem reduced_count : reducedRoster.length = 122 := by decide
theorem reduced_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · left
    intro k d hk hd
    exact Nat.le_trans (h k d hk hd) (by decide)
  · by_cases hc : (BB6.Agent31ThreeHole.tableOK e.2 p115 || BB6.Agent31ThreeHole.tableOK e.2 p119) = true
    · left
      rcases Bool.or_eq_true.mp hc with h115 | h119
      · have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ h115
        have hb := all115 m (heq ▸ hp)
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide)
      · have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ h119
        have hb := all119 m (heq ▸ hp)
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hc⟩,hp⟩
#print axioms reduced_count
#print axioms reduced_sound
end BB6.Agent8Six

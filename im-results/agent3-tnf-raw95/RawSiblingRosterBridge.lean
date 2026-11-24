import Raw95Data
import Raw105Data
import PureFourHoleResiduals
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3SiblingRoster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent44SourceRoster
abbrev p95 := BB6.Agent3Raw95.p95
abbrev p105 := BB6.Agent3Raw105.p105
def reducedRoster := pureRemainingRootRoster.filter fun e =>
  !(BB6.Agent31ThreeHole.tableOK e.2 p95 || BB6.Agent31ThreeHole.tableOK e.2 p105)
theorem reduced_count : reducedRoster.length = 122 := by decide
theorem reduced_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases pureRemainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · by_cases h95 : BB6.Agent31ThreeHole.tableOK e.2 p95 = true
    · left
      exact BB6.Agent3Raw95.all95 m (BB6.Agent31ThreeHole.tableOK_sound _ _ h95 ▸ hp)
    · by_cases h105 : BB6.Agent31ThreeHole.tableOK e.2 p105 = true
      · left
        exact BB6.Agent3Raw105.all105 m (BB6.Agent31ThreeHole.tableOK_sound _ _ h105 ▸ hp)
      · right
        exact ⟨e,List.mem_filter.mpr ⟨he,by simp [h95,h105]⟩,hp⟩
#print axioms reduced_count
#print axioms reduced_sound
end BB6.Agent3SiblingRoster

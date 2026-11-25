import Raw73Data
import Raw80Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Five
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent8Raw73 BB6.Agent8Raw80
def closedKey (p : PartialMachine) : Bool :=
  BB6.Agent31ThreeHole.tableOK p p73 || BB6.Agent31ThreeHole.tableOK p p80
noncomputable def reducedRoster := remainingRootRoster.filter fun e => !closedKey e.2
theorem reduced_count : reducedRoster.length = 122 := by decide
theorem reduced_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · by_cases hc : closedKey e.2 = true
    · left
      have hc' : BB6.Agent31ThreeHole.tableOK e.2 p73 = true ∨ BB6.Agent31ThreeHole.tableOK e.2 p80 = true := by
        simpa only [closedKey, Bool.or_eq_true] using hc
      rcases hc' with h73 | h80
      · have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ h73
        have hb := all73 m (heq ▸ hp)
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide)
      · have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ h80
        have hb := all80 m (heq ▸ hp)
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide)
    · right
      exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hc⟩,hp⟩
#print axioms reduced_count
#print axioms reduced_sound
end BB6.Agent8Five

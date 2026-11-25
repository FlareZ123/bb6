import Raw117Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw117Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent8Raw117

def covered (p : PartialMachine) : Bool := BB6.Agent31ThreeHole.tableOK p p117
theorem covered_count :
    (remainingRootRoster.filter fun e => covered e.2).length = 1 := by decide

theorem covered_sound (p : PartialMachine) (h : covered p = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 1291 m := by
  have heq := BB6.Agent31ThreeHole.tableOK_sound _ _ h
  exact all117 m (heq ▸ hm)

noncomputable def reducedRoster := remainingRootRoster.filter fun e => !(covered e.2)
theorem reduced_count : reducedRoster.length = 123 := by decide

theorem reduced_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 1291 m ∨ ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · left
    intro k d hk hd
    exact Nat.le_trans (h k d hk hd) (by decide)
  · cases hc : covered e.2 with
    | true => exact Or.inl (covered_sound e.2 hc m hp)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hc]⟩,hp⟩

#print axioms covered_count
#print axioms covered_sound
#print axioms reduced_count
#print axioms reduced_sound
#print axioms exact117
end BB6.Agent8Raw117Roster

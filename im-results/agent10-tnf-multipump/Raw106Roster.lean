import Raw106Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw106Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent10Raw106
def covered (p : PartialMachine) : Bool := sameTable p p106
theorem covered_sound (p : PartialMachine) (h : covered p = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 395 m := by
  have he := sameTable_sound h
  have hb := all106 m (he ▸ hm)
  intro k d hk hd
  exact Nat.le_trans (hb k d hk hd) (by decide)
noncomputable def reducedRoster := remainingRootRoster.filter fun e => !(covered e.2)
theorem reduced_count : reducedRoster.length = 123 := by decide
theorem reduced_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · cases hc : covered e.2 with
    | true => exact Or.inl (covered_sound e.2 hc m hp)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hc]⟩,hp⟩
#print axioms reduced_count
#print axioms reduced_sound
end BB6.Agent10Raw106Roster

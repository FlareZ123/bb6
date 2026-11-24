import Wide133Data
import FourHoleResidualRoster
namespace BB6.Agent7Wide133
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def reducedRoster133 : List (List Move × PartialMachine) :=
  remainingRootRoster.filter fun e => !(sameTable e.2 wideParent)
theorem reducedRoster133_count : reducedRoster133.length = 123 := by decide
theorem reducedRoster133_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ reducedRoster133, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with hb | ⟨e, he, hp⟩
  · exact Or.inl hb
  · cases hcheck : sameTable e.2 wideParent with
    | true =>
      have heq := sameTable_sound hcheck
      have hw := BB6.Agent7Wide133.all_completions_weighted m (heq ▸ hp)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hw k d hk hd) (by decide))
    | false =>
      exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [hcheck]⟩, hp⟩
#print axioms reducedRoster133_count
#print axioms reducedRoster133_sound
end BB6.Agent7Wide133

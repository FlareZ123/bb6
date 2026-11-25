import Raw120Complete
import Raw121Canonical77Graft
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120Canonical76Graft
open BB6Coverage BB6.Agent50TNFPilot BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement BB6.Agent11Raw121Canonical77Graft
open BB6.Agent3Raw120 BB6.Agent3Raw120Complete

noncomputable def roster75 := graftRoster p120 [] roster76

theorem parent_present :
    ∃ e ∈ roster76, sameTable e.2 p120 = true := by decide

theorem roster75_count : roster75.length = 75 := by decide

theorem raw120_root : p120 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem base_widened :
    ∀ m, compatible root m → WeightedBound 224707 m ∨
      ∃ e ∈ roster76, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases roster76_sound m hm with h | h
  · left
    intro k d hk hd
    exact Nat.le_trans (h k d hk hd) (by decide)
  · exact Or.inr h

/-- The 7014 root dichotomy must be widened, since the raw120 parent
    contains a genuinely later weighted halter. -/
theorem roster75_sound :
    ∀ m, compatible root m → WeightedBound 224707 m ∨
      ∃ e ∈ roster75, TNFQuotientCompatible e.2 m :=
  graftRoster_sound raw120_root base_widened
    (fun m hm => Or.inl (allRaw120 m hm))

theorem exact_at_target (B : Nat) (hB : 224707 ≤ B)
    (hLeaves : ∀ e ∈ roster75, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster75_sound hLeaves champ

#print axioms parent_present
#print axioms roster75_count
#print axioms roster75_sound
#print axioms exact_at_target
end BB6.Agent3Raw120Canonical76Graft

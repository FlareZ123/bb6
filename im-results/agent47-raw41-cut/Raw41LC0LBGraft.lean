import Raw41LC0LBClosed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

noncomputable def afterLC0LB := roster.filter fun e => !(sameTable e.2 Raw41LC0LB_p)

theorem lc0lb_unique : (roster.filter fun e => sameTable e.2 Raw41LC0LB_p).length = 1 := by decide +kernel
theorem afterLC0LB_count : afterLC0LB.length = 228 := by decide +kernel
theorem afterLC0LB_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterLC0LB, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases roster_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases h : sameTable e.2 Raw41LC0LB_p with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h]⟩,hq⟩
    | true =>
      have eq : e.2 = Raw41LC0LB_p := sameTable_sound h
      have hb := Raw41LC0LB_bound m (eq ▸ hq)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ afterLC0LB, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB afterLC0LB_sound hLeaves champ

#print axioms lc0lb_unique
#print axioms afterLC0LB_count
#print axioms afterLC0LB_sound
#print axioms exact_at_target
end BB6.Agent47Raw41

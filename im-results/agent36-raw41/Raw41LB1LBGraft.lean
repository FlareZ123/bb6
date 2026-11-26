import Raw41LB1LBClosed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

def afterLB1LB := canonicalRemaining.filter fun e => !(sameTable e.2 Raw41LB1LB_p)

theorem lb1lb_unique : (canonicalRemaining.filter fun e => sameTable e.2 Raw41LB1LB_p).length = 1 := by decide +kernel
theorem afterLB1LB_count : afterLB1LB.length = 152 := by decide +kernel

theorem afterLB1LB_sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 207 m ∨ ∃ e ∈ afterLB1LB, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases canonical_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · cases h : sameTable e.2 Raw41LB1LB_p with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h]⟩,hq⟩
    | true => exact Or.inl (Raw41LB1LB_bound m ((sameTable_sound h) ▸ hq))

#print axioms afterLB1LB_sound
#print axioms afterLB1LB_count
end BB6.Agent47Raw41

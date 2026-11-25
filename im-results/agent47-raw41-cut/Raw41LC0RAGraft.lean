import Raw41LC0RAClosed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

noncomputable def afterLC0RA := roster.filter fun e => !(sameTable e.2 Raw41LC0RA_p)

theorem lc0ra_unique : (roster.filter fun e => sameTable e.2 Raw41LC0RA_p).length = 1 := by decide +kernel
theorem afterLC0RA_count : afterLC0RA.length = 228 := by decide +kernel
theorem afterLC0RA_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterLC0RA, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases roster_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases h : sameTable e.2 Raw41LC0RA_p with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h]⟩,hq⟩
    | true =>
      have eq : e.2 = Raw41LC0RA_p := sameTable_sound h
      have hb := Raw41LC0RA_bound m (eq ▸ hq)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))

theorem exact_at_target_after_LC0RA (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ afterLC0RA, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB afterLC0RA_sound hLeaves champ

-- The previously checked LC0LB component may be ingested independently;
-- retain its exact quotient-bound theorem as an explicit input to this join.
abbrev lc0lbParent : PartialMachine := refine (child ⟨false,false,2⟩) (2,true) (some ⟨false,false,1⟩)
noncomputable def afterBothLC := afterLC0RA.filter fun e => !(sameTable e.2 lc0lbParent)

theorem lc0lb_unique_after_lc0ra : (afterLC0RA.filter fun e => sameTable e.2 lc0lbParent).length = 1 := by decide +kernel
theorem afterBothLC_count : afterBothLC.length = 227 := by decide +kernel
theorem afterBothLC_sound
    (hLC0LB : ∀ m, TNFQuotientCompatible lc0lbParent m → WeightedBound 229 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterBothLC, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases afterLC0RA_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases h : sameTable e.2 lc0lbParent with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h]⟩,hq⟩
    | true =>
      have eq : e.2 = lc0lbParent := sameTable_sound h
      have hb := hLC0LB m (eq ▸ hq)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))

#print axioms lc0ra_unique
#print axioms afterLC0RA_count
#print axioms afterLC0RA_sound
#print axioms exact_at_target_after_LC0RA
#print axioms lc0lb_unique_after_lc0ra
#print axioms afterBothLC_count
#print axioms afterBothLC_sound
end BB6.Agent47Raw41

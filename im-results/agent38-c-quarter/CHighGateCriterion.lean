import CFiniteSafetyBridge

namespace BB6Agent38

/-- Exact stopping iff for the original published Machine C acceleration,
    with the entire first 15,743 thin-gateway indices excluded globally. -/
theorem published_stops_iff_large_thin :
    (∃ s : S, BB6CLine.Reach s ∧ BB6CLine.nextC s = none) ↔
    (∃ j : Nat, 15743 ≤ j ∧ BB6CLine.Reach (0,2*j,4*j+10)) := by
  rw [BB6CLine.stops_iff_thin]
  constructor
  · rintro ⟨j,hj⟩
    have hlarge : 15743 ≤ j := by
      by_cases hh : 15743 ≤ j
      · exact hh
      · have hsmall : j ≤ 15742 := by omega
        exact (source_all_thin_indices_le_15742_unreachable j hsmall hj).elim
    exact ⟨j,hlarge,hj⟩
  · rintro ⟨j,_,hj⟩
    exact ⟨j,hj⟩

#print axioms published_stops_iff_large_thin
end BB6Agent38

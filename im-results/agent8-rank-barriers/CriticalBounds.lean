import CriticalReach

namespace BB6Rank

/-- The critical family parameter cannot be zero on the blank-tape trajectory. -/
theorem critical_index_pos {n j : Nat}
    (h : runSteps nextC n (5,0,1) = some (0,2*j,5)) : 0 < j := by
  have hr := nextC_run_rank_monotone n (5,0,1) (0,2*j,5) h
  simp only [rankC] at hr
  omega

/-- Quantitative lower bound on a critical index after n macro steps. -/
theorem critical_index_growth {n j : Nat}
    (h : runSteps nextC n (5,0,1) = some (0,2*j,5)) :
    37 + n ≤ (4*j+5)*(4*j+6) := by
  have hr := nextC_start_space_bound n (0,2*j,5) h
  have he : rankC (0,2*j,5) = 4*j+5 := by
    simp only [rankC]
    omega
  rw [he] at hr
  exact hr

/-- A reachable critical family must have a positive parameter. -/
theorem nextC_stops_iff_positive_critical :
    CollatzStops nextC (5,0,1) ↔
      ∃ n j, runSteps nextC n (5,0,1) = some (0,2*(j+1),5) := by
  rw [nextC_stops_iff_critical]
  constructor
  · rintro ⟨n, j, hj⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
      exact ⟨j - 1, by have hh := critical_index_pos hj; omega⟩
    exact ⟨n, j', hj⟩
  · rintro ⟨n, j, hj⟩
    exact ⟨n, j+1, hj⟩

end BB6Rank

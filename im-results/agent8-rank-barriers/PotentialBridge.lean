import CLine
import PotentialC

namespace Agent8Potential

theorem source_nextC_eq : BB6Rank.nextC = BB6CLine.nextC := by
  funext s
  rfl

theorem source_reach_has_time {s : Nat × Nat × Nat} (h : BB6CLine.Reach s) :
    ∃ n : Nat, BB6Rank.runSteps BB6Rank.nextC n (5,0,1) = some s := by
  induction h with
  | init => exact ⟨0, rfl⟩
  | next p q hp ht ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n+1, ?_⟩
      simp only [BB6Rank.runSteps, hn, Option.bind_some]
      simpa only [source_nextC_eq] using ht

/-- Sharpened potential bound for the published Machine C blank orbit. -/
theorem source_critical_time_bound {j : Nat}
    (h : BB6CLine.Reach (0,2*j,5)) :
    ∃ n : Nat, BB6Rank.runSteps BB6Rank.nextC n (5,0,1) = some (0,2*j,5) ∧
      44 + 2*n ≤ (4*j+5)*(4*j+8) := by
  obtain ⟨n, hn⟩ := source_reach_has_time h
  exact ⟨n, hn, BB6Rank.nextC_critical_time_bound hn⟩

#print axioms source_nextC_eq
#print axioms source_critical_time_bound
end Agent8Potential

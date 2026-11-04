import PositiveFan
import S4SourceShape

namespace S4Collision

theorem compact_source_equivalence (T : List Nat) :
    S4SourceShape.sourceReduced T = compactNext T := by
  rw [S4SourceShape.sourceReduced_eq_compactNext, compactNext_eq_source]

theorem source_unbounded_positive_halting_indegree (n : Nat) :
    ∃ (P : Nat → List Nat) (y : List Nat),
      (∀ x ∈ y, 0 < x) ∧
      (∀ i, ∀ x ∈ P i, 0 < x) ∧
      S4SourceShape.sourceReduced y = none ∧
      (∀ i, i ≤ n → S4SourceShape.sourceReduced (P i) = some y) ∧
      (∀ i j, i ≤ n → j ≤ n → P i = P j → i = j) := by
  simpa only [compact_source_equivalence] using unbounded_positive_halting_indegree n

theorem sourceRun_eq_run (n : Nat) (T : List Nat) :
    S4SourceShape.sourceRun n T = run n (some T) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (S4SourceShape.sourceRun n T).bind S4SourceShape.sourceReduced =
        (run n (some T)).bind compactNext
      rw [ih]
      cases h : run n (some T) with
      | none => simp [h]
      | some U => simpa [h] using compact_source_equivalence U

theorem source_rooted_collision :
    ∃ A B : List Nat,
      S4SourceShape.sourceRun 13 [42,12,8,5] = some A ∧
      A ≠ B ∧
      S4SourceShape.sourceReduced A = S4SourceShape.sourceReduced B := by
  obtain ⟨A,B,hA,hNe,hEq⟩ := actual_rooted_collision
  refine ⟨A,B,?_,hNe,?_⟩
  · rw [sourceRun_eq_run]; exact hA
  · simpa only [compact_source_equivalence] using hEq

#print axioms compact_source_equivalence
#print axioms source_unbounded_positive_halting_indegree
#print axioms source_rooted_collision
end S4Collision

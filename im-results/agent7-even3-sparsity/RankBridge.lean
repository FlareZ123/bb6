import EightThree
import RankBase

/-!
Transport the authentic Agent1 blank-reachability predicate into the original
P1 rank-monotone iterator and certify the exceptional short gateway is absent.
-/

namespace BB6.Agent7EightThree

private theorem g_agree (k c : Nat) :
    BB6.Agent1.G k c = BB6.P1Reduction.G k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h : c < 2*k
    · rw [BB6.Agent1.G,BB6.P1Reduction.G]
      simp only [h,dite_true]
      exact ih _ (by omega) _
    · by_cases h2 : c≤2*k+1
      · rw [BB6.Agent1.G,BB6.P1Reduction.G]
        simp [h,h2]
      · rw [BB6.Agent1.G,BB6.P1Reduction.G]
        simp [h,h2]

private theorem t_agree (a c : Nat) :
    BB6.Agent1.T a c=BB6.P1Reduction.T a c := by
  simp only [BB6.Agent1.T,BB6.P1Reduction.T,g_agree]

/-- Exact translation from original Agent1 source reachability into its
    identical P1Reduction acceleration, preserving every finite step. -/
theorem reach_to_iter (a c : Nat) (hr : BB6.Agent1.Reach a c) :
    ∃ n : Nat, BB6.P1Reduction.iterT n (2,1) = some (a,c) := by
  induction hr with
  | init => exact ⟨0,rfl⟩
  | next a c b d hprev ht ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨n+1,?_⟩
    have ht' : BB6.P1Reduction.T a c=some (b,d) := by
      rwa [←t_agree]
    rw [BB6.Agent7.iterT_add,hn]
    simpa [BB6.P1Reduction.iterT,ht']

/-- Rank 17 is first reached at time eight at (0,17), certifying that
    (2,15) can never occur on the authentic deterministic blank orbit. -/
theorem no_two_fifteen : ¬BB6.Agent1.Reach 2 15 := by
  intro hr
  obtain ⟨n,hn⟩ := reach_to_iter 2 15 hr
  have htrace : BB6.P1Reduction.iterT 7 (2,1) = some (5,9) := by
    rw [← BB6.Agent7.iterFast_correct]
    decide
  have hstep : BB6.P1Reduction.T 5 9 = some (0,17) := by
    rw [← BB6.Agent7.Tfast_correct]
    decide
  have no := BB6.Agent7.no_target_bracket 7 (5,9) (0,17) (2,15)
    htrace hstep (by decide) (by decide) (by decide)
  exact no n hn

#print axioms reach_to_iter
#print axioms no_two_fifteen
end BB6.Agent7EightThree

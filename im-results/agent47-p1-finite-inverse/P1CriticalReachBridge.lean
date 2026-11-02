import P1CriticalList
import P1CriticalArithmetic
import P1NoRootOne
import P1Gate

namespace BB6.Agent47P1
open BB6.P1Reduction

/-- Original blank-entry P1 critical halting candidates at *every even
index n>=4* must have a strictly positive inverse G-feeder belonging to
the explicitly finite criticalRootList n (<= log2(n+2)+1 candidates).
This is a necessary gateway, not a decision of P1 halting. -/
theorem actual_even_critical_requires_log_feeder (n : Nat)
    (hn : 4 ≤ n) (he : n%2=0)
    (hr : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) :
    ∃ k c, (k,c) ∈ criticalRootList n ∧
      2≤c ∧ BB6.Agent1.Reach (2*k-4) (c+4) := by
  obtain ⟨hlargeTarget,hmodTarget⟩ :=
    critical_even_target_form n hn he
  obtain ⟨hlargeHub,hmodHub⟩ :=
    critical_even_hub_form n hn he
  have hbridge :=
    BB6.Agent50P1.critical_target_implies_three
      (14*2^n-2*n-10) hlargeTarget hmodTarget hr
  have hhub : BB6.Agent1.Reach (14*2^n-2*n-16) 3 := by
    have heq :
        (14*2^n-2*n-10)-6 = 14*2^n-2*n-16 := by
      have hpow := n_plus_two_lt_pow n hn
      omega
    simpa only [heq] using hbridge
  have hno : ∀ k, ¬ GAncestor (14*2^n-2*n-16) 3 k 1 := by
    intro k
    exact critical_hub_no_one n k hn
  obtain ⟨k,c,hancestor,hpositive,hprior⟩ :=
    BB6.Agent50P1.positive_G_feeder
      (14*2^n-2*n-16) 3 hlargeHub hmodHub (by decide)
      hno hhub
  exact ⟨k,c,(critical_ancestor_iff_mem n k c hn).mp hancestor,
    hpositive,hprior⟩

/-- Infinite candidate family exclusion reduces to finitely many predecessors.
    The log bound remains uniform in every natural n, without residue splitting. -/
theorem no_even_critical_of_finite_feeders (n : Nat)
    (hn : 4 ≤ n) (he : n%2=0)
    (h : ∀ k c, (k,c) ∈ criticalRootList n → 2≤c →
      ¬BB6.Agent1.Reach (2*k-4) (c+4)) :
    ¬BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  obtain ⟨k,c,hmem,hc,hreach⟩ :=
    actual_even_critical_requires_log_feeder n hn he hr
  exact h k c hmem hc hreach

#print axioms actual_even_critical_requires_log_feeder
#print axioms no_even_critical_of_finite_feeders
end BB6.Agent47P1

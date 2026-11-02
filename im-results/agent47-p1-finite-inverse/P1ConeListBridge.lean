import P1FiniteInverse
import P1ResidualReach

namespace BB6.Agent47P1
open BB6.P1Reduction

/-- Exact finite-list certificate interface for the genuine blank orbit:
an all-time unreachable positive hub follows from an arithmetic one-input
obstruction and unreachability of every genuine inverse-list feeder. -/
theorem no_reach_of_inverse_list (b d : Nat)
    (hb : 8 ≤ b) (hmod : b%4=0) (hd : 0<d)
    (hpow : ∀ t, d+b/2+3 ≠ 4*2^t)
    (hchildren : ∀ k c, (k,c) ∈ inverseList b d →
       2≤c → ¬BB6.Agent1.Reach (2*k-4) (c+4)) :
    ¬BB6.Agent1.Reach b d := by
  intro hr
  have hno : ∀ k, ¬GAncestor b d k 1 :=
    (no_exceptional_one_iff b d (by omega) hmod).mpr hpow
  obtain ⟨k,c,hancestor,hc,hprev⟩ :=
    BB6.Agent50P1.positive_G_feeder b d hb hmod hd hno hr
  exact (hchildren k c ((inverse_iff_mem b d k c).mp hancestor) hc) hprev

#print axioms no_reach_of_inverse_list
end BB6.Agent47P1

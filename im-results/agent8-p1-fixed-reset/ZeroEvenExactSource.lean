import ZeroEvenExactCost
import ZeroEvenRigiditySource
import OddConeMass

namespace BB6.Agent8Zero
open BB6.Agent1Quarter BB6.Agent47P1

/-- An authentic P1 critical odd inverse history compatible with an
    original blank-reachable even-left successor with c=0 has a unique
    numeric feeder index j and exact cumulative inverse cost.
    This is a necessary gate condition, not a reachability theorem. -/
theorem source_critical_zero_even_exact_cost
    (n b d m t k : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2 ≤ k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    ∃ j : Nat,
      j<n ∧ t=j+2 ∧
      b=4*(2^j+j) ∧ d+2*j+3=10*2^j ∧
      7*2^j+n+m+j+5=7*2^n ∧
      7*2^n≤2*m+4*n+8 ∧
      3*2^n≤m := by
  have hroot := odd_cone_mass (14*2^n-2*n-16) 3 b d m hcone
  have hmass : b+d+2*m+2*n+13=14*2^n := by omega
  have hdodd : d%2=1 := by omega
  obtain ⟨j,ht,hb',hd'⟩ := source_zero_even_rigidity
    b d t k hb hb4 hdodd hinv hk hreach
  obtain ⟨hj,hEq,hCost,hStrong⟩ :=
    zero_even_exact_cost_and_lower n b d m j hn hmass hb' hd'
  exact ⟨j,hj,ht,hb',hd',hEq,hCost,hStrong⟩

#print axioms BB6.Agent8Zero.source_critical_zero_even_exact_cost
end BB6.Agent8Zero

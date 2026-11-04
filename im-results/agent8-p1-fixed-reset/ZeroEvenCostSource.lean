import ZeroEvenCostArithmetic
import OddConeMass
import InverseIff
import PosEvenForm

namespace BB6.Agent8Zero
open BB6.Agent1Quarter BB6.Agent47P1

/-- Exact original-source P1 critical odd histories whose inverseAt
has output c=0 and whose next even-left state is reachable from blank
must have cumulative inverse cost at least (3*2^n+6)/2. No reset
budget or inverse-length bound is assumed. -/
theorem source_critical_zero_even_exit_large_cost
    (n b d m t k : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    3*2^n+6≤2*m := by
  have hdom : n+4≤2^n := n_plus_four_le_pow n (by omega)
  have hroot := odd_cone_mass (14*2^n-2*n-16) 3 b d m hcone
  have hmass : b+d+2*m+2*n+13=14*2^n := by omega
  have hdodd : d%2=1 := by omega
  obtain ⟨hpower,hlinear⟩ :=
    (inverseAt_iff_power_mass b d t k 0 (by omega) hb4 hdodd).mp hinv
  have hpower' : d+b/2+3=3*2^t := by omega
  have hlinear' : 2*k+2*t+1=b+d := by omega
  have hleft : (2*k-4)%2=0 := by omega
  obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape
    (2*k-4) 4 hreach hleft (by decide) (by decide)
  have hreach' : 2*k+8=14*2^j := by omega
  exact c_zero_critical_math n b d m t k j hdom hmass
    hpower' hlinear' hreach'

#print axioms BB6.Agent8Zero.source_critical_zero_even_exit_large_cost
end BB6.Agent8Zero

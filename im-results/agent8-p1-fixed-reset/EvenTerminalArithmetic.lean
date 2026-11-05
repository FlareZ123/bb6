import Std

namespace BB6.Agent8AllEven

/-- An exact conservation law for a source odd-inverse feeder whose
    even-output successor has a genuine even-hub reset ancestor.
    Only the explicit arithmetic hypotheses are used. -/
theorem even_terminal_index_descent_core
    (n b d m t k c j s : Nat)
    (hroot : b+d+2*m+2*n+13=14*2^n)
    (hinv : 2*k+c+2*t+1+c%2=b+d)
    (heven : c%2=0)
    (hpow : 2*k+8=14*2^j)
    (hseed : s+2*j+2=2*k+c) :
    j<n ∧
    s+2*j+10=14*2^j+c ∧
    7*2^j+c/2+t+m+n+3=7*2^n ∧
    s+2*n+10+2*(t+m+j+3)=14*2^n := by
  have hmass : 7*2^j+c/2+t+m+n+3=7*2^n := by omega
  have hjn : j<n := by
    by_cases hlt : j<n
    · exact hlt
    · have hge : n≤j := by omega
      have hpmono : (2:Nat)^n≤2^j :=
        Nat.pow_le_pow_right (by decide) hge
      omega
  refine ⟨hjn, by omega, hmass, ?_⟩
  omega

/-- The even feeder's authentic earlier reset lies strictly below the
    critical counter corresponding to the current odd-cone exponent. -/
theorem even_terminal_seed_below_critical
    (n s t m j : Nat)
    (h : s+2*n+10+2*(t+m+j+3)=14*2^n) :
    s < 14*2^n-2*n-10 := by
  omega

#print axioms even_terminal_index_descent_core
#print axioms even_terminal_seed_below_critical
end BB6.Agent8AllEven

import EvenTerminalArithmetic
import ZeroEvenDescentSource

namespace BB6.Agent8AllEven
open BB6.Agent1Quarter BB6.Agent47P1

/-- Every genuinely blank-reachable even-output exit from the critical
    P1 source odd cone has an earlier authentic reset, at a strictly lower
    dyadic exponent, with exact inverse-cost and reset-height equations.
    The output c is any nonnegative even natural. -/
theorem source_all_even_exit_has_lower_reset_window
    (n b d m t k c : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,c)) (hk : 2≤k)
    (heven : c%2=0)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4)) :
    ∃ j s : Nat, j<n ∧
      BB6.Agent1.Reach 2 s ∧
      s+2*j+10=14*2^j+c ∧
      7*2^j+c/2+t+m+n+3=7*2^n ∧
      s+2*n+10+2*(t+m+j+3)=14*2^n ∧
      s<14*2^n-2*n-10 := by
  have hrootmass := odd_cone_mass (14*2^n-2*n-16) 3 b d m hcone
  have hroot : b+d+2*m+2*n+13=14*2^n := by omega
  have hdodd : d%2=1 := by omega
  obtain ⟨_, hinvmass⟩ :=
    (inverseAt_iff_power_mass b d t k c (by omega) hb4 hdodd).mp hinv
  obtain ⟨j,s,hs,hjpow,hjsum⟩ :=
    BB6.Agent1.even_hub_reset_seed (2*k-4) (c+4)
      hreach (by omega) (by omega) (by omega)
  have hpow : 2*k+8=14*2^j := by omega
  have hseed : s+2*j+2=2*k+c := by omega
  obtain ⟨hjn,hshape,hcost,hgap⟩ :=
    even_terminal_index_descent_core n b d m t k c j s
      hroot hinvmass heven hpow hseed
  have hsmall : s<14*2^n-2*n-10 :=
    even_terminal_seed_below_critical n s t m j hgap
  exact ⟨j,s,hjn,hs,hshape,hcost,hgap,hsmall⟩

/-- For a least genuinely reachable critical exponent n, any even
    source-exit candidate must be a strictly positive even overshoot
    of a lower-index critical threshold, with a strictly smaller
    genuinely reachable reset seed. No conclusion is drawn for c>=2. -/
theorem source_minimal_critical_even_exit_overshoots
    (n b d m t k c : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,c)) (hk : 2≤k)
    (heven : c%2=0)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4))
    (hminimal : ∀ q : Nat, q<n →
      ¬ BB6.Agent1.Reach 2 (14*2^q-2*q-10)) :
    ∃ j s : Nat, j<n ∧ 2≤c ∧
      BB6.Agent1.Reach 2 s ∧
      s+2*j+10=14*2^j+c ∧
      s+2*n+10+2*(t+m+j+3)=14*2^n := by
  obtain ⟨j,s,hjn,hs,hshape,_,hgap,_⟩ :=
    source_all_even_exit_has_lower_reset_window
      n b d m t k c hn hcone hb hb4 hinv hk heven hreach
  have hcpos : 2≤c := by
    by_cases hz : c=0
    · subst c
      exact False.elim
        (BB6.Agent8Descent.source_no_zero_even_exit_for_minimal_critical
          n b d m t k hn hcone hb hb4 hinv hk hreach hminimal)
    · omega
  exact ⟨j,s,hjn,hcpos,hs,hshape,hgap⟩

#print axioms source_all_even_exit_has_lower_reset_window
#print axioms source_minimal_critical_even_exit_overshoots
end BB6.Agent8AllEven

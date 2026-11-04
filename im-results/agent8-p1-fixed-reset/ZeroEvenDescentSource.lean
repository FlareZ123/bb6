import EvenSeed
import InverseIff
import OddConeMass

namespace BB6.Agent8Descent
open BB6.Agent1Quarter BB6.Agent47P1

/-- A genuine blank-reachable positive-even state with right counter four
    carries an earlier blank-reachable critical reset of the same exponent.
    This is an exact ancestry implication, using original EvenSeed. -/
theorem even_four_has_critical_reset
    (b q : Nat)
    (hreach : BB6.Agent1.Reach b 4)
    (hbeven : b%2=0)
    (hpow : b+12=14*2^q) :
    BB6.Agent1.Reach 2 (14*2^q-2*q-10) := by
  obtain ⟨j,s,hseed,hjpow,hsum⟩ :=
    BB6.Agent1.even_hub_reset_seed b 4 hreach hbeven
      (by decide) (by decide)
  have hjq : j=q := by
    by_cases hlt : j<q
    · have hltpow := Nat.pow_lt_pow_right
        (show 1<(2:Nat) by decide) hlt
      omega
    · by_cases hgt : q<j
      · have hgtpow := Nat.pow_lt_pow_right
          (show 1<(2:Nat) by decide) hgt
        omega
      · omega
  subst j
  have hseed_eq : s=14*2^q-2*q-10 := by omega
  simpa only [hseed_eq] using hseed

/-- An original-source zero-output terminal from a critical odd inverse cone,
    whose even successor is genuinely blank-reachable, produces a strictly
    smaller genuinely reachable critical reset index. All inverse depths and
    cumulative inverse costs are quantified without any cutoff. -/
theorem source_zero_even_exit_forces_lower_critical
    (n b d m t k : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    ∃ q : Nat, q<n ∧
      BB6.Agent1.Reach 2 (14*2^q-2*q-10) := by
  have hroot := odd_cone_mass (14*2^n-2*n-16) 3 b d m hcone
  have hmass : b+d+2*m+2*n+13=14*2^n := by omega
  have hdodd : d%2=1 := by omega
  obtain ⟨hp,hm⟩ := (inverseAt_iff_power_mass
    b d t k 0 (by omega) hb4 hdodd).mp hinv
  obtain ⟨q,s,hseed,hshape,hsum⟩ :=
    BB6.Agent1.even_hub_reset_seed
      (2*k-4) 4 hreach (by omega) (by decide) (by decide)
  have heq : 7*2^q+n+m+t+3=7*2^n := by omega
  have hqn : q<n := by
    by_cases hlt : q<n
    · exact hlt
    · have hge : n≤q := by omega
      have hpmono : (2:Nat)^n≤2^q :=
        Nat.pow_le_pow_right (by decide) hge
      omega
  have hseed_eq : s=14*2^q-2*q-10 := by omega
  refine ⟨q,hqn,?_⟩
  simpa only [hseed_eq] using hseed

/-- Therefore this terminal mechanism cannot occur for a least critical
    reset exponent on the genuine blank orbit. -/
theorem source_no_zero_even_exit_for_minimal_critical
    (n b d m t k : Nat) (hn : 14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4)
    (hminimal : ∀ q : Nat, q<n →
      ¬ BB6.Agent1.Reach 2 (14*2^q-2*q-10)) : False := by
  obtain ⟨q,hlt,hr⟩ := source_zero_even_exit_forces_lower_critical
    n b d m t k hn hcone hb hb4 hinv hk hreach
  exact hminimal q hlt hr

#print axioms BB6.Agent8Descent.even_four_has_critical_reset
#print axioms BB6.Agent8Descent.source_zero_even_exit_forces_lower_critical
#print axioms BB6.Agent8Descent.source_no_zero_even_exit_for_minimal_critical
end BB6.Agent8Descent

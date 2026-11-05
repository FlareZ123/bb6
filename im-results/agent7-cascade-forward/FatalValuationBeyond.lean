import FatalValuationUnbounded
set_option maxHeartbeats 0

namespace CascadeFatalValuation
open CascadeFirstFork CascadeManyShield

private theorem exponential_growth (N:Nat) : 8*2^N < 3^(N+3) :=by
  induction N with
  | zero=>decide
  | succ N ih=>
    rw [show N+1+3=N+3+1 by omega,Nat.pow_succ]
    rw [Nat.pow_succ]
    omega

private theorem fatal_below_growth (N n:Nat) (hn:4≤n) (h:n≤N):
  2*fatal n+5 < 3^(N+3):=by
  have hc:=fatal_close n hn
  have hp:2^n≤2^N:=Nat.pow_le_pow_right (by decide) h
  have hg:=exponential_growth N
  omega

/-- Arbitrarily far along the original surviving n≡4 mod6 fatal-index
    cylinder, the odd inverse input has arbitrarily high 3-adic valuation.
    This applies beyond any fixed finite source-machine cutoff. -/
theorem fatal_high_val_above_four (N v:Nat):
  ∃n:Nat,N<n ∧ n%6=4 ∧ (2*fatal n+5)%3^(v+1)=0:=by
  obtain ⟨n,hn,hres,hdiv⟩:=fatal_unbounded_3adic_four (N+v+3)
  have hbig:N<n:=by
    by_cases hle:n≤N
    · have hsmall:=fatal_below_growth N n hn hle
      have hpow:3^(N+3)≤3^((N+v+3)+1):=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hlt:2*fatal n+5<3^((N+v+3)+1):=by omega
      have hmod:=Nat.mod_eq_of_lt hlt
      rw [hmod] at hdiv
      omega
    · omega
  have hpowdiv:(3^(v+1):Nat) ∣ 3^((N+v+3)+1):=by
    have he:(N+v+3)+1=(v+1)+(N+3):=by omega
    refine ⟨3^(N+3),?_⟩
    rw [he,Nat.pow_add]
  have hsmall:(2*fatal n+5)%3^(v+1)=0:=
    Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans hpowdiv (Nat.dvd_of_mod_eq_zero hdiv))
  exact ⟨n,hbig,hres,hsmall⟩

/-- The n≡5 mod6 fatal-index cylinder also contains arbitrarily large
    indices with arbitrarily high 3-adic inverse numerators. -/
theorem fatal_high_val_above_five (N v:Nat):
  ∃n:Nat,N<n ∧ n%6=5 ∧ (2*fatal n+5)%3^(v+1)=0:=by
  obtain ⟨n,hn,hres,hdiv⟩:=fatal_unbounded_3adic_five (N+v+3)
  have hbig:N<n:=by
    by_cases hle:n≤N
    · have hsmall:=fatal_below_growth N n (by omega) hle
      have hpow:3^(N+3)≤3^((N+v+3)+1):=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hlt:2*fatal n+5<3^((N+v+3)+1):=by omega
      have hmod:=Nat.mod_eq_of_lt hlt
      rw [hmod] at hdiv
      omega
    · omega
  have hpowdiv:(3^(v+1):Nat) ∣ 3^((N+v+3)+1):=by
    have he:(N+v+3)+1=(v+1)+(N+3):=by omega
    refine ⟨3^(N+3),?_⟩
    rw [he,Nat.pow_add]
  have hsmall:(2*fatal n+5)%3^(v+1)=0:=
    Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans hpowdiv (Nat.dvd_of_mod_eq_zero hdiv))
  exact ⟨n,hbig,hres,hsmall⟩

#print axioms fatal_high_val_above_four
#print axioms fatal_high_val_above_five
end CascadeFatalValuation

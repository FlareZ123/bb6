import RayThirdNoRoot
set_option maxHeartbeats 0
namespace CascadeRayExceptionalDisjoint

private theorem pow_period_six (n:Nat):2^(n+6)%3=2^n%3:=by
  rw[Nat.pow_add];simp[Nat.mul_mod]
private theorem pow_mod_six (n:Nat):2^n%3=2^(n%6)%3:=by
  induction n using Nat.strongRecOn with
  | ind n ih=>
    by_cases hn:n<6
    · simp[Nat.mod_eq_of_lt hn]
    · have hm:n-6<n:=by omega
      have he:n=(n-6)+6:=by omega
      rw[he,pow_period_six,ih (n-6) hm]
      have hemod:((n-6)+6)%6=(n-6)%6:=by omega
      rw[hemod]

/-- A #746 t=1 odd-parent source height and its mandatory next even
    predecessor cannot both have ternary-divisible odd numerators.
    In particular their 27-divisibility exceptional branches are
    provably disjoint for every index in the surviving fatal sectors. -/
theorem two_tier_odd_numerators_disjoint (n h w:Nat) (hn:4≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hparent:2*h=2*2^n+w+(n-2)):
  (2*h+5)%3=0 → (2*w+5)%3≠0:=by
  intro hdiv
  have hpow:=pow_mod_six n
  rcases hsector with h4|h5
  · have hp:2^n%3=1:=by rw[hpow,h4]
    omega
  · have hp:2^n%3=2:=by rw[hpow,h5]
    omega

/-- The two simultaneously high-valuation alternatives of the exact
    t=1 fork selector cannot occur for the same source parent edge. -/
theorem not_both_exceptional (n h w:Nat) (hn:4≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hparent:2*h=2*2^n+w+(n-2)):
  ¬((2*h+5)%27=0 ∧ (2*w+5)%27=0):=by
  rintro ⟨ha,hb⟩
  have hm:(2*h+5)%3=0:=by omega
  have hw:(2*w+5)%3=0:=by omega
  exact (two_tier_odd_numerators_disjoint n h w hn hsector hparent hm) hw

#print axioms two_tier_odd_numerators_disjoint
#print axioms not_both_exceptional
end CascadeRayExceptionalDisjoint

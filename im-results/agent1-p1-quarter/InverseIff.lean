import MassInverse
import P1InverseLog
namespace BB6.Agent1Quarter
open BB6.Agent47P1
open BB6.P1Reduction

private theorem pow_two_injective (j k:Nat) (h:2^j=2^k) : j=k := by
  by_cases hlt:j<k
  · have hpow := Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hlt
    omega
  · by_cases hgt:k<j
    · have hpow := Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hgt
      omega
    · omega

/-- Exact linear/power Diophantine characterization of every source inverseAt
    value, including all depths and both parities of final counters. -/
theorem inverseAt_iff_power_mass (b d t k c : Nat)
    (hb:4≤b) (hmod:b%4=0) (hd:d%2=1) :
    inverseAt b d t = some (k,c) ↔
      d+b/2+3=2^t*(c+3) ∧
      2*k+c+2*t+1+c%2=b+d := by
  constructor
  · intro h
    exact ⟨inverseAt_power b d t k c h,
      inverseAt_exact_mass b d t k c hb hmod hd h⟩
  · rintro ⟨hp,hm⟩
    have hanc : ∃ x, GAncestor b d x c :=
      (ancestor_exists_iff_power b d c hb hmod).mpr ⟨t,hp⟩
    obtain ⟨x,hx⟩ := hanc
    obtain ⟨s,hs,_⟩ := inverseAt_complete b d x c hx
    have hp' := inverseAt_power b d s x c hs
    have hpow : 2^t=2^s :=
      Nat.eq_of_mul_eq_mul_right (by omega) (hp.symm.trans hp')
    have hts : t=s := pow_two_injective t s hpow
    subst s
    have hmass := inverseAt_exact_mass b d t x c hb hmod hd hs
    have hxk : x=k := by omega
    subst x
    exact hs

/-- Source GAncestor exactly iff a scalar dyadic equation and one linear
    counter-mass equation have a common natural depth. -/
theorem ancestor_iff_power_mass (b d k c : Nat)
    (hb:4≤b) (hmod:b%4=0) (hd:d%2=1) :
    GAncestor b d k c ↔
    ∃ t : Nat, d+b/2+3=2^t*(c+3) ∧
      2*k+c+2*t+1+c%2=b+d := by
  constructor
  · intro h
    obtain ⟨t,ht,_⟩ := inverseAt_complete b d k c h
    exact ⟨t, (inverseAt_iff_power_mass b d t k c hb hmod hd).mp ht⟩
  · rintro ⟨t,ht⟩
    exact inverseAt_sound b d t k c
      ((inverseAt_iff_power_mass b d t k c hb hmod hd).mpr ht)

#print axioms inverseAt_iff_power_mass
#print axioms ancestor_iff_power_mass
end BB6.Agent1Quarter

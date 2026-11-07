import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

/-!
Additional infinite congruence obstructions for Space Needle terminal feeders.

For a feeder valuation v, the source-certified terminal equation is
  2^(k+2)+3 = (2^(v+1)+3)*(2*q+3)+2*v.
If an odd modulus p divides both 2^(v+1)+3 and 2*v-3, this equation
forces p | 2^(k+2), contradicting coprimality of p and 2.

The existing SpaceNeedleClosed development already formalizes the p=5 and
p=7 families. This file formalizes the p=11 and p=13 families recorded in
the external Space Needle modular-obstruction analysis, and adds p=19 and
p=29 families. In particular, v=74 (already in the external finite
obstruction table) is extended to the full progression 74 mod 812.
These are exclusions of immediate terminal feeders for every q and k;
they do not prove that the actual blank-root orbit avoids all remaining
terminal feeders.
-/

namespace BB6.Agent48.SpaceNeedleObstructionFamilies

open BB6.Agent48.SpaceNeedle

private theorem pow10_mod11 : 2^10 % 11 = 1 := by decide
private theorem pow3_mod11 : 2^3 % 11 = 8 := by decide

private theorem pow10_period11 (n : Nat) : (2^10)^n % 11 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih, pow10_mod11]

/-- The denominator 2^(v+1)+3 is divisible by 11 when v=62 mod 110. -/
theorem family11_denominator (t : Nat) :
    11 ∣ 2^(62+110*t+1)+3 := by
  have hexp : 62+110*t+1 = 3+10*(6+11*t) := by omega
  have hpow : 2^(62+110*t+1)%11=8 := by
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow3_mod11, pow10_period11]
  apply Nat.dvd_iff_mod_eq_zero.mpr
  rw [Nat.add_mod, hpow]

/-- The valuation correction 2v-3 is divisible by 11 on the same family. -/
theorem family11_remainder (t : Nat) :
    ∃ u, 2*(62+110*t)=3+11*u := by
  exact ⟨11+20*t, by omega⟩

/-- No valuation v=62 mod 110 can feed any terminal power-of-two counter. -/
theorem no_62_mod_110_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (62+110*t))) ≠
      some (.N (haltTower k)) := by
  exact no_common_modulus_into_power q (62+110*t) k 11
    (by decide) (by decide) (family11_denominator t) (family11_remainder t)

private theorem pow12_mod13 : 2^12 % 13 = 1 := by decide
private theorem pow10_mod13 : 2^10 % 13 = 10 := by decide

private theorem pow12_period13 (n : Nat) : (2^12)^n % 13 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih, pow12_mod13]

/-- The denominator 2^(v+1)+3 is divisible by 13 when v=21 mod 156. -/
theorem family13_denominator (t : Nat) :
    13 ∣ 2^(21+156*t+1)+3 := by
  have hexp : 21+156*t+1 = 10+12*(1+13*t) := by omega
  have hpow : 2^(21+156*t+1)%13=10 := by
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow10_mod13, pow12_period13]
  apply Nat.dvd_iff_mod_eq_zero.mpr
  rw [Nat.add_mod, hpow]

/-- The valuation correction 2v-3 is divisible by 13 on the same family. -/
theorem family13_remainder (t : Nat) :
    ∃ u, 2*(21+156*t)=3+13*u := by
  exact ⟨3+24*t, by omega⟩

/-- No valuation v=21 mod 156 can feed any terminal power-of-two counter. -/
theorem no_21_mod_156_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (21+156*t))) ≠
      some (.N (haltTower k)) := by
  exact no_common_modulus_into_power q (21+156*t) k 13
    (by decide) (by decide) (family13_denominator t) (family13_remainder t)

private theorem pow18_mod19 : 2^18 % 19 = 1 := by decide
private theorem pow4_mod19 : 2^4 % 19 = 16 := by decide

private theorem pow18_period19 (n : Nat) : (2^18)^n % 19 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih, pow18_mod19]

/-- The denominator 2^(v+1)+3 is divisible by 19 when v=201 mod 342. -/
theorem family19_denominator (t : Nat) :
    19 ∣ 2^(201+342*t+1)+3 := by
  have hexp : 201+342*t+1 = 4+18*(11+19*t) := by omega
  have hpow : 2^(201+342*t+1)%19=16 := by
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow4_mod19, pow18_period19]
  apply Nat.dvd_iff_mod_eq_zero.mpr
  rw [Nat.add_mod, hpow]

/-- The valuation correction 2v-3 is divisible by 19 on the same family. -/
theorem family19_remainder (t : Nat) :
    ∃ u, 2*(201+342*t)=3+19*u := by
  exact ⟨21+36*t, by omega⟩

/-- New infinite obstruction: no valuation v=201 mod 342 feeds a halt. -/
theorem no_201_mod_342_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (201+342*t))) ≠
      some (.N (haltTower k)) := by
  exact no_common_modulus_into_power q (201+342*t) k 19
    (by decide) (by decide) (family19_denominator t) (family19_remainder t)

private theorem pow28_mod29 : 2^28 % 29 = 1 := by decide
private theorem pow19_mod29 : 2^19 % 29 = 26 := by decide

private theorem pow28_period29 (n : Nat) : (2^28)^n % 29 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih, pow28_mod29]

/-- The denominator 2^(v+1)+3 is divisible by 29 when v=74 mod 812. -/
theorem family29_denominator (t : Nat) :
    29 ∣ 2^(74+812*t+1)+3 := by
  have hexp : 74+812*t+1 = 19+28*(2+29*t) := by omega
  have hpow : 2^(74+812*t+1)%29=26 := by
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow19_mod29, pow28_period29]
  apply Nat.dvd_iff_mod_eq_zero.mpr
  rw [Nat.add_mod, hpow]

/-- The valuation correction 2v-3 is divisible by 29 on the same family. -/
theorem family29_remainder (t : Nat) :
    ∃ u, 2*(74+812*t)=3+29*u := by
  exact ⟨5+56*t, by omega⟩

/-- New infinite obstruction: the known v=74 exception extends to all v=74 mod 812. -/
theorem no_74_mod_812_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (74+812*t))) ≠
      some (.N (haltTower k)) := by
  exact no_common_modulus_into_power q (74+812*t) k 29
    (by decide) (by decide) (family29_denominator t) (family29_remainder t)

#print axioms no_62_mod_110_halving_into_power
#print axioms no_21_mod_156_halving_into_power
#print axioms no_201_mod_342_halving_into_power
#print axioms no_74_mod_812_halving_into_power

end BB6.Agent48.SpaceNeedleObstructionFamilies

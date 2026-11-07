import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

/-!
Periodic congruence obstructions for Space Needle terminal feeders.

The source-certified terminal-predecessor identity is
  2^(k+2)+3 = (2^(v+1)+3)*(2*q+3)+2*v.
If an odd modulus p divides both 2^(v+1)+3 and 2*v-3, then this identity
forces p | 2^(k+2), impossible because p is coprime to 2.

The generic theorem below lifts one modular obstruction to an entire
arithmetic progression of valuations. It formalizes the p=11 and p=13
families from the external Space Needle modular analysis, and gives two
additional progressions: v = 201 mod 342 (p=19) and v = 74 mod 812 (p=29).
The p=29 family extends the obstruction at v=74 to every member of that
progression. These are exclusions of immediate terminal feeders for all q
and k; they do not establish blank-root nonreachability of the remaining
feeders.
-/

namespace BB6.Agent48.SpaceNeedleObstructionFamilies

open BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

private theorem pow_period_mod (p L n : Nat) (hp : 1 < p)
    (hperiod : 2^L % p = 1) : (2^L)^n % p = 1 := by
  induction n with
  | zero =>
      have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
      simpa using h1
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hperiod]
      rw [Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)

private theorem pow_mod_progression (p r L n : Nat) (hp : 1 < p)
    (hperiod : 2^L % p = 1) : 2^(r+L*n) % p = 2^r % p := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow_period_mod p L n hp hperiod]
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

private theorem progression_denominator (p r L s v0 t : Nat)
    (hp : 3 < p)
    (hperiod : 2^L % p = 1)
    (hexp : v0+1 = r+L*s)
    (hbase : p ∣ 2^r+3) :
    p ∣ 2^(v0+L*t+1)+3 := by
  have hExp : v0+L*t+1 = r+L*(s+t) := by
    calc
      v0+L*t+1 = (v0+1)+L*t := by omega
      _ = (r+L*s)+L*t := by rw [hexp]
      _ = r+L*(s+t) := by rw [Nat.mul_add]; omega
  have hpow : 2^(v0+L*t+1)%p = 2^r%p := by
    rw [hExp]
    exact pow_mod_progression p r L (s+t) (by omega) hperiod
  have h3 : 3%p=3 := Nat.mod_eq_of_lt (by omega)
  have hbaseMod : (2^r%p+3)%p=0 := by
    have h := (Nat.dvd_iff_mod_eq_zero).mp hbase
    rw [Nat.add_mod, h3] at h
    exact h
  apply Nat.dvd_iff_mod_eq_zero.mpr
  rw [Nat.add_mod, hpow, h3]
  exact hbaseMod

private theorem progression_correction (p L v0 t : Nat)
    (hbase : ∃ u, 2*v0=3+p*u)
    (hstep : p ∣ 2*L) :
    ∃ u, 2*(v0+L*t)=3+p*u := by
  rcases hbase with ⟨u,hu⟩
  rcases hstep with ⟨w,hw⟩
  refine ⟨u+w*t, ?_⟩
  calc
    2*(v0+L*t) = 2*v0+2*(L*t) := by rw [Nat.mul_add]
    _ = (3+p*u)+(2*L)*t := by rw [hu, ←Nat.mul_assoc]
    _ = (3+p*u)+(p*w)*t := by rw [hw]
    _ = 3+p*(u+w*t) := by rw [Nat.mul_assoc, Nat.add_assoc, ←Nat.mul_add]

private theorem pow_multiple_period (p L n : Nat) (hp : 1 < p)
    (hperiod : 2^L % p = 1) : 2^(L*n)%p=1 := by
  rw [Nat.pow_mul]
  exact pow_period_mod p L n hp hperiod

/-- One modular obstruction lifts to an infinite progression of feeder
valuations. The exponent and correction congruences are explicit inputs. -/
theorem no_terminal_on_periodic_valuation_progression
    (p r L s v0 q k t : Nat)
    (hp : 3 < p)
    (hc : Nat.Coprime p 2)
    (hperiod : 2^L % p = 1)
    (hexp : v0+1 = r+L*s)
    (hbase : p ∣ 2^r+3)
    (hbaseCorrection : ∃ u, 2*v0=3+p*u)
    (hstep : p ∣ 2*L) :
    highLevelNext (.N (oddTower q (v0+L*t))) ≠
      some (.N (haltTower k)) := by
  exact no_common_modulus_into_power q (v0+L*t) k p
    (by omega) hc
    (progression_denominator p r L s v0 t hp hperiod hexp hbase)
    (progression_correction p L v0 t hbaseCorrection hstep)

/-- No valuation v=62 mod 110 can feed any terminal power-of-two counter. -/
theorem no_62_mod_110_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (62+110*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^110%11=1 := by
    change 2^(10*11)%11=1
    exact pow_multiple_period 11 10 11 (by omega) (by decide)
  exact no_terminal_on_periodic_valuation_progression 11 63 110 0 62 q k t
    (by omega) (by decide) hperiod (by omega) (by decide)
    (by refine ⟨11, ?_⟩; omega)
    (by refine ⟨20, ?_⟩; omega)

/-- No valuation v=21 mod 156 can feed any terminal power-of-two counter. -/
theorem no_21_mod_156_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (21+156*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^156%13=1 := by
    change 2^(12*13)%13=1
    exact pow_multiple_period 13 12 13 (by omega) (by decide)
  exact no_terminal_on_periodic_valuation_progression 13 22 156 0 21 q k t
    (by omega) (by decide) hperiod (by omega) (by decide)
    (by refine ⟨3, ?_⟩; omega)
    (by refine ⟨24, ?_⟩; omega)

/-- New infinite obstruction: no valuation v=201 mod 342 feeds a halt. -/
theorem no_201_mod_342_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (201+342*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^342%19=1 := by
    change 2^(18*19)%19=1
    exact pow_multiple_period 19 18 19 (by omega) (by decide)
  exact no_terminal_on_periodic_valuation_progression 19 202 342 0 201 q k t
    (by omega) (by decide) hperiod (by omega) (by decide)
    (by refine ⟨21, ?_⟩; omega)
    (by refine ⟨36, ?_⟩; omega)

/-- New infinite obstruction: the known v=74 obstruction extends to all
v=74 mod 812. -/
theorem no_74_mod_812_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (74+812*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^812%29=1 := by
    change 2^(28*29)%29=1
    exact pow_multiple_period 29 28 29 (by omega) (by decide)
  exact no_terminal_on_periodic_valuation_progression 29 75 812 0 74 q k t
    (by omega) (by decide) hperiod (by omega) (by decide)
    (by refine ⟨5, ?_⟩; omega)
    (by refine ⟨56, ?_⟩; omega)

#print axioms no_terminal_on_periodic_valuation_progression
#print axioms no_62_mod_110_halving_into_power
#print axioms no_21_mod_156_halving_into_power
#print axioms no_201_mod_342_halving_into_power
#print axioms no_74_mod_812_halving_into_power

end BB6.Agent48.SpaceNeedleObstructionFamilies

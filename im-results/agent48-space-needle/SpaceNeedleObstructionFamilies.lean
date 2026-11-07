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
    calc
      2^342%19 = (2^18)^19%19 := by
        rw [show 342=18*19 by omega, Nat.pow_mul]
      _ = 1 := pow_period_mod 19 18 19 (by omega) (by decide)
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
    calc
      2^812%29 = (2^28)^29%29 := by
        rw [show 812=28*29 by omega, Nat.pow_mul]
      _ = 1 := pow_period_mod 29 28 29 (by omega) (by decide)
  exact no_terminal_on_periodic_valuation_progression 29 75 812 0 74 q k t
    (by omega) (by decide) hperiod (by omega) (by decide)
    (by refine ⟨5, ?_⟩; omega)
    (by refine ⟨56, ?_⟩; omega)


/-- A stronger residue obstruction: if the required residue of 2^(k+2)
is absent modulo m, then the source cannot feed a halt. -/
theorem no_terminal_by_modular_residue_avoidance
    (q v k m : Nat)
    (hm : 0 < m)
    (hden : m ∣ 2^(v+1)+3)
    (havoid : ∀ n, (2^n+3)%m ≠ (2*v)%m) :
    highLevelNext (.N (oddTower q v)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have heq := (predecessor_power_identity q v k).mp hhalt
  have hdenMod : (2^(v+1)+3)%m=0 := Nat.dvd_iff_mod_eq_zero.mp hden
  have hprodMod : ((2^(v+1)+3)*(2*q+3))%m=0 := by
    rw [Nat.mul_mod, hdenMod]
    simp
  have hmod : (2^(k+2)+3)%m=(2*v)%m := by
    calc
      (2^(k+2)+3)%m = ((2^(v+1)+3)*(2*q+3)+2*v)%m := by rw [heq]
      _ = (((2^(v+1)+3)*(2*q+3))%m+(2*v)%m)%m := by rw [Nat.add_mod]
      _ = (0+(2*v)%m)%m := by rw [hprodMod]
      _ = (2*v)%m := by
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ hm)
  exact havoid (k+2) hmod

private theorem pow_plus_three_mod_seven (n : Nat) :
    (2^n+3)%7=0 ∨ (2^n+3)%7=4 ∨ (2^n+3)%7=5 := by
  rcases pow_two_mod_seven n with h1|h2|h4
  · rw [Nat.add_mod, h1]
    decide
  · rw [Nat.add_mod, h2]
    decide
  · rw [Nat.add_mod, h4]
    decide

/-- The 7-adic residue test excludes four complete valuation classes modulo 21.
The v=19 class was already present in SpaceNeedleClosed; v=1,4,10 are new
infinite progressions. -/
theorem no_7_mod_21_halving_into_power (q k t v0 : Nat)
    (hv0 : v0=1 ∨ v0=4 ∨ v0=10 ∨ v0=19) :
    highLevelNext (.N (oddTower q (21*t+v0))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^21%7=1 := by decide
  have hden : 7 ∣ 2^(21*t+v0+1)+3 := by
    rcases hv0 with h1|h4|h10|h19
    · subst v0
      exact progression_denominator 7 2 21 0 1 t (by omega) hperiod (by omega) (by decide)
    · subst v0
      exact progression_denominator 7 5 21 0 4 t (by omega) hperiod (by omega) (by decide)
    · subst v0
      exact progression_denominator 7 11 21 0 10 t (by omega) hperiod (by omega) (by decide)
    · subst v0
      exact progression_denominator 7 20 21 0 19 t (by omega) hperiod (by omega) (by decide)
  have havoid : ∀ n, (2^n+3)%7 ≠ (2*(21*t+v0))%7 := by
    intro n
    have hleft := pow_plus_three_mod_seven n
    rcases hv0 with h1|h4|h10|h19
    · subst v0
      have htarget : (2*(21*t+1))%7=2 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
    · subst v0
      have htarget : (2*(21*t+4))%7=1 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
    · subst v0
      have htarget : (2*(21*t+10))%7=6 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
    · subst v0
      have htarget : (2*(21*t+19))%7=3 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
  exact no_terminal_by_modular_residue_avoidance q (21*t+v0) k 7
    (by omega) hden havoid

private theorem pow_two_multiple39_mod79 (n : Nat) : 2^(39*n)%79=1 := by
  exact pow_multiple_period 79 39 n (by omega) (by decide)

private theorem pow_two_mod79_ne_15 (n : Nat) : 2^n%79 ≠ 15 := by
  intro h
  have hleft : (2^n)^39%79=1 := by
    rw [←Nat.pow_mul, Nat.mul_comm n 39]
    exact pow_two_multiple39_mod79 n
  have hright : (2^n)^39%79=15^39%79 := by
    rw [Nat.pow_mod, h]
  have htarget : 15^39%79=78 := by decide
  rw [htarget] at hright
  omega

private theorem pow_two_mod79_ne_14 (n : Nat) : 2^n%79 ≠ 14 := by
  intro h
  have hleft : (2^n)^39%79=1 := by
    rw [←Nat.pow_mul, Nat.mul_comm n 39]
    exact pow_two_multiple39_mod79 n
  have hright : (2^n)^39%79=14^39%79 := by
    rw [Nat.pow_mod, h]
  have htarget : 14^39%79=78 := by decide
  rw [htarget] at hright
  omega

private theorem no_two_plus_three_mod79_eq18 (n : Nat) :
    (2^n+3)%79 ≠ 18 := by
  intro h
  have h3 : 3%79=3 := by decide
  rw [Nat.add_mod, h3] at h
  have hlt : 2^n%79 < 79 := Nat.mod_lt _ (by decide)
  have hpow : 2^n%79=15 := by omega
  exact pow_two_mod79_ne_15 n hpow

private theorem no_two_plus_three_mod79_eq17 (n : Nat) :
    (2^n+3)%79 ≠ 17 := by
  intro h
  have h3 : 3%79=3 := by decide
  rw [Nat.add_mod, h3] at h
  have hlt : 2^n%79 < 79 := Nat.mod_lt _ (by decide)
  have hpow : 2^n%79=14 := by omega
  exact pow_two_mod79_ne_14 n hpow

/-- The p=79 subgroup obstruction extends the known v=9 feeder obstruction
to v=9 mod 3081. -/
theorem no_9_mod_3081_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (9+3081*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^3081%79=1 := by
    calc
      2^3081%79 = (2^39)^79%79 := by
        rw [show 3081=39*79 by omega, Nat.pow_mul]
      _ = 1 := pow_period_mod 79 39 79 (by omega) (by decide)
  have hden : 79 ∣ 2^(9+3081*t+1)+3 :=
    progression_denominator 79 10 3081 0 9 t (by omega) hperiod (by omega) (by decide)
  have havoid : ∀ n, (2^n+3)%79 ≠ (2*(9+3081*t))%79 := by
    intro n
    have htarget : (2*(9+3081*t))%79=18 := by omega
    rw [htarget]
    exact no_two_plus_three_mod79_eq18 n
  exact no_terminal_by_modular_residue_avoidance q (9+3081*t) k 79
    (by omega) hden havoid

/-- A second p=79 subgroup obstruction, for v=48 mod 3081. -/
theorem no_48_mod_3081_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (48+3081*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^3081%79=1 := by
    calc
      2^3081%79 = (2^39)^79%79 := by
        rw [show 3081=39*79 by omega, Nat.pow_mul]
      _ = 1 := pow_period_mod 79 39 79 (by omega) (by decide)
  have hden : 79 ∣ 2^(48+3081*t+1)+3 :=
    progression_denominator 79 49 3081 0 48 t (by omega) hperiod (by omega) (by decide)
  have havoid : ∀ n, (2^n+3)%79 ≠ (2*(48+3081*t))%79 := by
    intro n
    have htarget : (2*(48+3081*t))%79=17 := by omega
    rw [htarget]
    exact no_two_plus_three_mod79_eq17 n
  exact no_terminal_by_modular_residue_avoidance q (48+3081*t) k 79
    (by omega) hden havoid

private theorem pow_two_multiple51_mod103 (n : Nat) : 2^(51*n)%103=1 := by
  exact pow_multiple_period 103 51 n (by omega) (by decide)

private theorem pow_two_mod103_ne_12 (n : Nat) : 2^n%103 ≠ 12 := by
  intro h
  have hleft : (2^n)^51%103=1 := by
    rw [←Nat.pow_mul, Nat.mul_comm n 51]
    exact pow_two_multiple51_mod103 n
  have hright : (2^n)^51%103=12^51%103 := by
    rw [Nat.pow_mod, h]
  have htarget : 12^51%103=102 := by decide
  rw [htarget] at hright
  omega

private theorem no_two_plus_three_mod103_eq15 (n : Nat) :
    (2^n+3)%103 ≠ 15 := by
  intro h
  have h3 : 3%103=3 := by decide
  rw [Nat.add_mod, h3] at h
  have hlt : 2^n%103 < 103 := Nat.mod_lt _ (by decide)
  have hpow : 2^n%103=12 := by omega
  exact pow_two_mod103_ne_12 n hpow

/-- The p=103 subgroup obstruction extends v=59 to v=59 mod 5253. -/
theorem no_59_mod_5253_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (59+5253*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^5253%103=1 := by
    calc
      2^5253%103 = (2^51)^103%103 := by
        rw [show 5253=51*103 by omega, Nat.pow_mul]
      _ = 1 := pow_period_mod 103 51 103 (by omega) (by decide)
  have hden : 103 ∣ 2^(59+5253*t+1)+3 :=
    progression_denominator 103 60 5253 0 59 t (by omega) hperiod (by omega) (by decide)
  have havoid : ∀ n, (2^n+3)%103 ≠ (2*(59+5253*t))%103 := by
    intro n
    have htarget : (2*(59+5253*t))%103=15 := by omega
    rw [htarget]
    exact no_two_plus_three_mod103_eq15 n
  exact no_terminal_by_modular_residue_avoidance q (59+5253*t) k 103
    (by omega) hden havoid

#print axioms no_terminal_on_periodic_valuation_progression
#print axioms no_62_mod_110_halving_into_power
#print axioms no_21_mod_156_halving_into_power
#print axioms no_201_mod_342_halving_into_power
#print axioms no_74_mod_812_halving_into_power
#print axioms no_terminal_by_modular_residue_avoidance
#print axioms no_7_mod_21_halving_into_power
#print axioms no_9_mod_3081_halving_into_power
#print axioms no_48_mod_3081_halving_into_power
#print axioms no_59_mod_5253_halving_into_power

end BB6.Agent48.SpaceNeedleObstructionFamilies

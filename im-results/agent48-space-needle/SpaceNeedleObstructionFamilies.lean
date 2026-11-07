import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

/-!
Modular and CRT obstructions for Space Needle terminal feeders.

The source-certified terminal-predecessor identity is
  2^(k+2)+3 = (2^(v+1)+3)*(2*q+3)+2*v.
If m divides 2^(v+1)+3, every terminal feeder must therefore satisfy
  (2^(k+2)+3) % m = (2*v) % m.
The public modular-identity theorem exposes this necessary condition;
residue avoidance and incompatible exponent congruences turn it into
non-halting feeder exclusions.

The periodic lift theorem formalizes arithmetic progressions, including
p=11,13,19,29 zero-residue families and p=7,79,103 nonzero-residue
families. The file also formalizes two composite-modulus CRT obstructions
at v=7 and v=12, where each prime-power factor separately admits a
discrete logarithm but the required exponents are incompatible.

These results exclude immediate terminal feeders. They do not establish
blank-root nonreachability of all remaining feeder configurations.
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


private theorem pow_period_mod_base (p g L n : Nat) (hp : 1 < p)
    (hperiod : g^L%p=1) : (g^L)^n%p=1 := by
  induction n with
  | zero => exact Nat.mod_eq_of_lt hp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hperiod]
      rw [Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)

private theorem pow_multiple_period_base (p g L n : Nat) (hp : 1 < p)
    (hperiod : g^L%p=1) : g^(L*n)%p=1 := by
  rw [Nat.pow_mul]
  exact pow_period_mod_base p g L n hp hperiod

private theorem pow_mod_progression_base (p g r L n : Nat) (hp : 1 < p)
    (hperiod : g^L%p=1) : g^(r+L*n)%p=g^r%p := by
  rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod,pow_period_mod_base p g L n hp hperiod]
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

private theorem no_power_residue_of_order_power_mismatch_base (p g L r : Nat)
    (hp : 1 < p) (hperiod : g^L%p=1) (hwrong : r^L%p ≠ 1)
    (n : Nat) : g^n%p ≠ r := by
  intro h
  have hleft : (g^n)^L%p=1 := by
    rw [←Nat.pow_mul, Nat.mul_comm n L]
    exact pow_multiple_period_base p g L n hp hperiod
  have hright : (g^n)^L%p=r^L%p := by rw [Nat.pow_mod, h]
  rw [hleft] at hright
  exact hwrong hright.symm


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


/-- Necessary modular identity for every terminal feeder. -/
theorem terminal_feeder_modular_identity
    (q v k m : Nat) (hm : 0 < m)
    (hden : m ∣ 2^(v+1)+3)
    (hhalt : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    (2^(k+2)+3)%m=(2*v)%m := by
  have heq := (predecessor_power_identity q v k).mp hhalt
  have hdenMod : (2^(v+1)+3)%m=0 := Nat.dvd_iff_mod_eq_zero.mp hden
  have hprodMod : ((2^(v+1)+3)*(2*q+3))%m=0 := by
    rw [Nat.mul_mod, hdenMod]
    simp
  calc
    (2^(k+2)+3)%m = ((2^(v+1)+3)*(2*q+3)+2*v)%m := by rw [heq]
    _ = (((2^(v+1)+3)*(2*q+3))%m+(2*v)%m)%m := by rw [Nat.add_mod]
    _ = (0+(2*v)%m)%m := by rw [hprodMod]
    _ = (2*v)%m := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ hm)

/-- A stronger residue obstruction: if the required residue of 2^(k+2)
is absent modulo m, then the source cannot feed a halt. -/
theorem no_terminal_by_modular_residue_avoidance
    (q v k m : Nat)
    (hm : 0 < m)
    (hden : m ∣ 2^(v+1)+3)
    (havoid : ∀ n, (2^n+3)%m ≠ (2*v)%m) :
    highLevelNext (.N (oddTower q v)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  exact havoid (k+2) (terminal_feeder_modular_identity q v k m hm hden hhalt)

private theorem pow_two_mod5_eq1_implies_n_mod4_eq0 (n : Nat)
    (h5 : 2^n%5=1) : n%4=0 := by
  have hperiod :2^4%5=1 := by decide
  have hred :2^n%5=2^(n%4)%5 := by
    calc
      2^n%5=2^(n%4+4*(n/4))%5 := by rw [Nat.mod_add_div n 4]
      _ =2^(n%4)%5 := pow_mod_progression 5 (n%4) 4 (n/4) (by omega) hperiod
  have hlt :n%4<4 := Nat.mod_lt _ (by decide)
  by_cases h0:n%4=0
  · exact h0
  by_cases h1:n%4=1
  · rw [hred,h1] at h5
    simp at h5
  by_cases h2:n%4=2
  · rw [hred,h2] at h5
    simp at h5
  have h3:n%4=3 := by omega
  rw [hred,h3] at h5
  simp at h5

/-- Composite CRT obstruction at v=7: the mod-7 and mod-37 exponent
requirements are incompatible. -/
theorem no_7_terminal_feeder (q k : Nat) :
    highLevelNext (.N (oddTower q 7)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have h7den : 7 ∣ 2^(7+1)+3 := by decide
  have h37den : 37 ∣ 2^(7+1)+3 := by decide
  have h7 : (2^(k+2)+3)%7=(2*7)%7 :=
    terminal_feeder_modular_identity q 7 k 7 (by omega) h7den hhalt
  have h37 : (2^(k+2)+3)%37=(2*7)%37 :=
    terminal_feeder_modular_identity q 7 k 37 (by omega) h37den hhalt
  have h3_7 : 3%7=3 := by decide
  rw [Nat.add_mod,h3_7] at h7
  have h7lt : 2^(k+2)%7<7 := Nat.mod_lt _ (by decide)
  have h7pow : 2^(k+2)%7=4 := by omega
  have h3_37 : 3%37=3 := by decide
  rw [Nat.add_mod,h3_37] at h37
  have h37lt : 2^(k+2)%37<37 := Nat.mod_lt _ (by decide)
  have h37pow : 2^(k+2)%37=11 := by omega
  have hperiod3 : 2^3%7=1 := by decide
  have hred : 2^(k+2)%7=2^((k+2)%3)%7 := by
    calc
      2^(k+2)%7=2^((k+2)%3+3*((k+2)/3))%7 := by rw [Nat.mod_add_div (k+2) 3]
      _ = 2^((k+2)%3)%7 := pow_mod_progression 7 ((k+2)%3) 3 ((k+2)/3) (by omega) hperiod3
  have hmod3 : (k+2)%3=2 := by
    by_cases h0 : (k+2)%3=0
    · rw [hred,h0] at h7pow
      simp at h7pow
    by_cases h1 : (k+2)%3=1
    · rw [hred,h1] at h7pow
      simp at h7pow
    have hlt : (k+2)%3<3 := Nat.mod_lt _ (by decide)
    omega
  have hdecomp : k+2=3*((k+2)/3)+2 := by
    have hn := Nat.mod_add_div (k+2) 3
    rw [hmod3] at hn
    omega
  have hrewrite : 2^(3*((k+2)/3)+2)%37=(8^((k+2)/3)*4)%37 := by
    rw [Nat.pow_add,Nat.pow_mul]
  rw [hdecomp,hrewrite] at h37pow
  have h4 : 4%37=4 := by decide
  rw [Nat.mul_mod,h4] at h37pow
  have h8lt : 8^((k+2)/3)%37<37 := Nat.mod_lt _ (by decide)
  have h8pow : 8^((k+2)/3)%37=12 := by omega
  have hwrong : 12^12%37≠1 := by decide
  exact (no_power_residue_of_order_power_mismatch_base 37 8 12 12 (by omega) (by decide) hwrong ((k+2)/3)) h8pow

/-- Composite CRT obstruction at v=12: mod 5 forces k+2 even, while
mod 11 forces it into a power-of-four class that cannot yield -1. -/
theorem no_12_terminal_feeder (q k : Nat) :
    highLevelNext (.N (oddTower q 12)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have h5den : 5 ∣ 2^(12+1)+3 := by decide
  have h11den : 11 ∣ 2^(12+1)+3 := by decide
  have h5 : (2^(k+2)+3)%5=(2*12)%5 :=
    terminal_feeder_modular_identity q 12 k 5 (by omega) h5den hhalt
  have h11 : (2^(k+2)+3)%11=(2*12)%11 :=
    terminal_feeder_modular_identity q 12 k 11 (by omega) h11den hhalt
  have h3_5 :3%5=3 := by decide
  rw [Nat.add_mod,h3_5] at h5
  have h5lt :2^(k+2)%5<5 := Nat.mod_lt _ (by decide)
  have h5pow :2^(k+2)%5=1 := by omega
  have h3_11 :3%11=3 := by decide
  rw [Nat.add_mod,h3_11] at h11
  have h11lt :2^(k+2)%11<11 := Nat.mod_lt _ (by decide)
  have h11pow :2^(k+2)%11=10 := by omega
  have hmod4 := pow_two_mod5_eq1_implies_n_mod4_eq0 (k+2) h5pow
  have heven : (k+2)%2=0 := by omega
  have hdecomp : k+2=2*((k+2)/2) := by
    have hn := Nat.mod_add_div (k+2) 2
    rw [heven] at hn
    omega
  have hrewrite : 2^(2*((k+2)/2))%11=(4^((k+2)/2))%11 := by
    rw [Nat.pow_mul]
  rw [hdecomp,hrewrite] at h11pow
  have hperiod4 :4^5%11=1 := by decide
  have hwrong10 :10^5%11≠1 := by decide
  exact (no_power_residue_of_order_power_mismatch_base 11 4 5 10 (by omega) hperiod4 hwrong10 ((k+2)/2)) h11pow


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
    highLevelNext (.N (oddTower q (v0+21*t))) ≠
      some (.N (haltTower k)) := by
  have hperiod : 2^21%7=1 := by decide
  have hden : 7 ∣ 2^(v0+21*t+1)+3 := by
    rcases hv0 with h1|h4|h10|h19
    · subst v0
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (progression_denominator 7 2 21 0 1 t (by decide) hperiod (by decide) (by decide))
    · subst v0
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (progression_denominator 7 5 21 0 4 t (by decide) hperiod (by decide) (by decide))
    · subst v0
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (progression_denominator 7 11 21 0 10 t (by decide) hperiod (by decide) (by decide))
    · subst v0
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (progression_denominator 7 20 21 0 19 t (by decide) hperiod (by decide) (by decide))
  have havoid : ∀ n, (2^n+3)%7 ≠ (2*(v0+21*t))%7 := by
    intro n
    have hleft := pow_plus_three_mod_seven n
    rcases hv0 with h1|h4|h10|h19
    · subst v0
      have htarget : (2*(1+21*t))%7=2 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
    · subst v0
      have htarget : (2*(4+21*t))%7=1 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
    · subst v0
      have htarget : (2*(10+21*t))%7=6 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
    · subst v0
      have htarget : (2*(19+21*t))%7=3 := by omega
      rw [htarget]
      rcases hleft with h|h|h <;> omega
  exact no_terminal_by_modular_residue_avoidance q (v0+21*t) k 7
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
#print axioms terminal_feeder_modular_identity
#print axioms no_7_terminal_feeder
#print axioms no_12_terminal_feeder
/-- Composite CRT obstruction at v=18: modulo 29 forces k+2 even,
while modulo 179 forces k+2 odd. -/
theorem no_18_terminal_feeder (q k : Nat) :
    highLevelNext (.N (oddTower q 18)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have h29den : 29 ∣ 2^(18+1)+3 := by decide
  have h179den : 179 ∣ 2^(18+1)+3 := by decide
  have h29 : (2^(k+2)+3)%29=(2*18)%29 :=
    terminal_feeder_modular_identity q 18 k 29 (by omega) h29den hhalt
  have h179 : (2^(k+2)+3)%179=(2*18)%179 :=
    terminal_feeder_modular_identity q 18 k 179 (by omega) h179den hhalt
  have h3_29 : 3%29=3 := by decide
  rw [Nat.add_mod,h3_29] at h29
  have h29lt : 2^(k+2)%29<29 := Nat.mod_lt _ (by decide)
  have h29pow : 2^(k+2)%29=4 := by omega
  have h3_179 : 3%179=3 := by decide
  rw [Nat.add_mod,h3_179] at h179
  have h179lt : 2^(k+2)%179<179 := Nat.mod_lt _ (by decide)
  have h179pow : 2^(k+2)%179=33 := by omega
  have h2_14 : 2^14%29=28 := by decide
  have h4_14 : 4^14%29=1 := by decide
  have h2_89 : 2^89%179=178 := by decide
  have h33_89 : 33^89%179=178 := by decide
  have h29left : (2^(k+2))^14%29=4^14%29 := by rw [Nat.pow_mod,h29pow]
  have h29rewrite : (2^(k+2))^14%29=(2^14)^(k+2)%29 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 14,Nat.pow_mul]
  have h29base : (2^14)^(k+2)%29=28^(k+2)%29 := by rw [Nat.pow_mod,h2_14]
  have h28pow : 28^(k+2)%29=1 := by
    rw [h4_14] at h29left
    rw [h29rewrite,h29base] at h29left
    exact h29left
  have h28period : 28^2%29=1 := by decide
  have h28red : 28^(k+2)%29=28^((k+2)%2)%29 := by
    calc
      28^(k+2)%29=28^((k+2)%2+2*((k+2)/2))%29 := by rw [Nat.mod_add_div (k+2) 2]
      _ = 28^((k+2)%2)%29 :=
        pow_mod_progression_base 29 28 ((k+2)%2) 2 ((k+2)/2) (by omega) h28period
  have heven : (k+2)%2=0 := by
    by_cases h0 : (k+2)%2=0
    · exact h0
    have hlt : (k+2)%2<2 := Nat.mod_lt _ (by decide)
    have h1 : (k+2)%2=1 := by omega
    rw [h28red,h1] at h28pow
    simp at h28pow
  have h179left : (2^(k+2))^89%179=33^89%179 := by rw [Nat.pow_mod,h179pow]
  have h179rewrite : (2^(k+2))^89%179=(2^89)^(k+2)%179 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 89,Nat.pow_mul]
  have h179base : (2^89)^(k+2)%179=178^(k+2)%179 := by rw [Nat.pow_mod,h2_89]
  have h178pow : 178^(k+2)%179=178 := by
    rw [h33_89] at h179left
    rw [h179rewrite,h179base] at h179left
    exact h179left
  have h178period : 178^2%179=1 := by decide
  have h178red : 178^(k+2)%179=178^((k+2)%2)%179 := by
    calc
      178^(k+2)%179=178^((k+2)%2+2*((k+2)/2))%179 := by rw [Nat.mod_add_div (k+2) 2]
      _ = 178^((k+2)%2)%179 :=
        pow_mod_progression_base 179 178 ((k+2)%2) 2 ((k+2)/2) (by omega) h178period
  have hodd : (k+2)%2=1 := by
    by_cases h0 : (k+2)%2=0
    · rw [h178red,h0] at h178pow
      simp at h178pow
    have hlt : (k+2)%2<2 := Nat.mod_lt _ (by decide)
    omega
  omega


private theorem pow_two_mod5_eq3_implies_n_mod4_eq3 (n : Nat)
    (h5 : 2^n%5=3) : n%4=3 := by
  have hperiod :2^4%5=1 := by decide
  have hred :2^n%5=2^(n%4)%5 := by
    calc
      2^n%5=2^(n%4+4*(n/4))%5 := by rw [Nat.mod_add_div n 4]
      _ =2^(n%4)%5 := pow_mod_progression 5 (n%4) 4 (n/4) (by omega) hperiod
  have hlt :n%4<4 := Nat.mod_lt _ (by decide)
  by_cases h0:n%4=0
  · rw [hred,h0] at h5
    simp at h5
  by_cases h1:n%4=1
  · rw [hred,h1] at h5
    simp at h5
  by_cases h2:n%4=2
  · rw [hred,h2] at h5
    simp at h5
  omega

/-- Composite CRT obstruction at v=28: mod 5 forces k+2 odd,
while a projected mod-1901 residue forces it even. -/
theorem no_28_terminal_feeder (q k : Nat) :
    highLevelNext (.N (oddTower q 28)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have h5den : 5 ∣ 2^(28+1)+3 := by decide
  have h1901den : 1901 ∣ 2^(28+1)+3 := by decide
  have h5 : (2^(k+2)+3)%5=(2*28)%5 :=
    terminal_feeder_modular_identity q 28 k 5 (by omega) h5den hhalt
  have h1901 : (2^(k+2)+3)%1901=(2*28)%1901 :=
    terminal_feeder_modular_identity q 28 k 1901 (by omega) h1901den hhalt
  have h3_5 :3%5=3 := by decide
  rw [Nat.add_mod,h3_5] at h5
  have h5lt :2^(k+2)%5<5 := Nat.mod_lt _ (by decide)
  have h5pow :2^(k+2)%5=3 := by omega
  have h3_1901 :3%1901=3 := by decide
  rw [Nat.add_mod,h3_1901] at h1901
  have h1901lt :2^(k+2)%1901<1901 := Nat.mod_lt _ (by decide)
  have h1901pow :2^(k+2)%1901=53 := by omega
  have hmod4 := pow_two_mod5_eq3_implies_n_mod4_eq3 (k+2) h5pow
  have hodd : (k+2)%2=1 := by omega
  have h2_95 :2^95%1901=692 := by decide
  have h53_95 :53^95%1901=1224 := by decide
  have h1224_10 :1224^10%1901=1 := by decide
  have h692_10 :692^10%1901=1900 := by decide
  have hleft :(2^(k+2))^95%1901=53^95%1901 := by rw [Nat.pow_mod,h1901pow]
  have hrewrite :(2^(k+2))^95%1901=(2^95)^(k+2)%1901 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 95,Nat.pow_mul]
  have hbase :(2^95)^(k+2)%1901=692^(k+2)%1901 := by rw [Nat.pow_mod,h2_95]
  have h692pow :692^(k+2)%1901=1224 := by
    rw [h53_95] at hleft
    rw [hrewrite,hbase] at hleft
    exact hleft
  have hleft10 :(692^(k+2))^10%1901=1224^10%1901 := by rw [Nat.pow_mod,h692pow]
  have hrewrite10 :(692^(k+2))^10%1901=(692^10)^(k+2)%1901 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 10,Nat.pow_mul]
  have hbase10 :(692^10)^(k+2)%1901=1900^(k+2)%1901 := by rw [Nat.pow_mod,h692_10]
  have h1900pow :1900^(k+2)%1901=1 := by
    rw [h1224_10] at hleft10
    rw [hrewrite10,hbase10] at hleft10
    exact hleft10
  have hperiod :1900^2%1901=1 := by decide
  have hred :1900^(k+2)%1901=1900^((k+2)%2)%1901 := by
    calc
      1900^(k+2)%1901=1900^((k+2)%2+2*((k+2)/2))%1901 := by rw [Nat.mod_add_div (k+2) 2]
      _ =1900^((k+2)%2)%1901 :=
        pow_mod_progression_base 1901 1900 ((k+2)%2) 2 ((k+2)/2) (by omega) hperiod
  have heven : (k+2)%2=0 := by
    by_cases h0:(k+2)%2=0
    · exact h0
    have hlt :(k+2)%2<2 := Nat.mod_lt _ (by decide)
    have h1:(k+2)%2=1 := by omega
    rw [hred,h1] at h1900pow
    simp at h1900pow
  omega

/-- Composite CRT obstruction at v=35: the mod-61 and mod-523
conditions force different residues of k+2 modulo 3. -/
theorem no_35_terminal_feeder (q k : Nat) :
    highLevelNext (.N (oddTower q 35)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have h61den :61 ∣ 2^(35+1)+3 := by decide
  have h523den :523 ∣ 2^(35+1)+3 := by decide
  have h61 : (2^(k+2)+3)%61=(2*35)%61 :=
    terminal_feeder_modular_identity q 35 k 61 (by omega) h61den hhalt
  have h523 : (2^(k+2)+3)%523=(2*35)%523 :=
    terminal_feeder_modular_identity q 35 k 523 (by omega) h523den hhalt
  have h3_61 :3%61=3 := by decide
  rw [Nat.add_mod,h3_61] at h61
  have h61lt :2^(k+2)%61<61 := Nat.mod_lt _ (by decide)
  have h61pow :2^(k+2)%61=6 := by omega
  have h3_523 :3%523=3 := by decide
  rw [Nat.add_mod,h3_523] at h523
  have h523lt :2^(k+2)%523<523 := Nat.mod_lt _ (by decide)
  have h523pow :2^(k+2)%523=67 := by omega
  have h2_20 :2^20%61=47 := by decide
  have h6_20 :6^20%61=47 := by decide
  have h47_3 :47^3%61=1 := by decide
  have hleft61 :(2^(k+2))^20%61=6^20%61 := by rw [Nat.pow_mod,h61pow]
  have hrewrite61 :(2^(k+2))^20%61=(2^20)^(k+2)%61 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 20,Nat.pow_mul]
  have hbase61 :(2^20)^(k+2)%61=47^(k+2)%61 := by rw [Nat.pow_mod,h2_20]
  have h47pow :47^(k+2)%61=47 := by
    rw [h6_20] at hleft61
    rw [hrewrite61,hbase61] at hleft61
    exact hleft61
  have h47red :47^(k+2)%61=47^((k+2)%3)%61 := by
    calc
      47^(k+2)%61=47^((k+2)%3+3*((k+2)/3))%61 := by rw [Nat.mod_add_div (k+2) 3]
      _ =47^((k+2)%3)%61 :=
        pow_mod_progression_base 61 47 ((k+2)%3) 3 ((k+2)/3) (by omega) h47_3
  have hmod3_1 :(k+2)%3=1 := by
    by_cases h0:(k+2)%3=0
    · rw [h47red,h0] at h47pow
      simp at h47pow
    by_cases h2:(k+2)%3=2
    · rw [h47red,h2] at h47pow
      have h47sq :47^2%61=13 := by decide
      rw [h47sq] at h47pow
      omega
    have hlt :(k+2)%3<3 := Nat.mod_lt _ (by decide)
    omega
  have h2_174 :2^174%523=462 := by decide
  have h67_174 :67^174%523=60 := by decide
  have h462_3 :462^3%523=1 := by decide
  have hleft523 :(2^(k+2))^174%523=67^174%523 := by rw [Nat.pow_mod,h523pow]
  have hrewrite523 :(2^(k+2))^174%523=(2^174)^(k+2)%523 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 174,Nat.pow_mul]
  have hbase523 :(2^174)^(k+2)%523=462^(k+2)%523 := by rw [Nat.pow_mod,h2_174]
  have h462pow :462^(k+2)%523=60 := by
    rw [h67_174] at hleft523
    rw [hrewrite523,hbase523] at hleft523
    exact hleft523
  have h462red :462^(k+2)%523=462^((k+2)%3)%523 := by
    calc
      462^(k+2)%523=462^((k+2)%3+3*((k+2)/3))%523 := by rw [Nat.mod_add_div (k+2) 3]
      _ =462^((k+2)%3)%523 :=
        pow_mod_progression_base 523 462 ((k+2)%3) 3 ((k+2)/3) (by omega) h462_3
  have hmod3_2 :(k+2)%3=2 := by
    by_cases h0:(k+2)%3=0
    · rw [h462red,h0] at h462pow
      simp at h462pow
    by_cases h1:(k+2)%3=1
    · rw [h462red,h1] at h462pow
      have h462 :462%523=462 := by decide
      rw [h462] at h462pow
      omega
    have hlt :(k+2)%3<3 := Nat.mod_lt _ (by decide)
    omega
  omega

set_option exponentiation.threshold 10000 in
set_option maxRecDepth 8192 in
/-- Composite CRT obstruction at v=36: mod 25 forces k+2 to be
2 modulo 4, while a fourth-power projection modulo 35573 forces 0. -/
theorem no_36_terminal_feeder (q k : Nat) :
    highLevelNext (.N (oddTower q 36)) ≠ some (.N (haltTower k)) := by
  intro hhalt
  have h25den :25 ∣ 2^(36+1)+3 := by decide
  have h35573den :35573 ∣ 2^(36+1)+3 := by decide
  have h25 : (2^(k+2)+3)%25=(2*36)%25 :=
    terminal_feeder_modular_identity q 36 k 25 (by omega) h25den hhalt
  have h35573 : (2^(k+2)+3)%35573=(2*36)%35573 :=
    terminal_feeder_modular_identity q 36 k 35573 (by omega) h35573den hhalt
  have h3_25 :3%25=3 := by decide
  rw [Nat.add_mod,h3_25] at h25
  have h25lt :2^(k+2)%25<25 := Nat.mod_lt _ (by decide)
  have h25pow :2^(k+2)%25=19 := by omega
  have h3_35573 :3%35573=3 := by decide
  rw [Nat.add_mod,h3_35573] at h35573
  have h35573lt :2^(k+2)%35573<35573 := Nat.mod_lt _ (by decide)
  have h35573pow :2^(k+2)%35573=69 := by omega
  have h2_5 :2^5%25=7 := by decide
  have h19_5 :19^5%25=24 := by decide
  have hleft25 :(2^(k+2))^5%25=19^5%25 := by rw [Nat.pow_mod,h25pow]
  have hrewrite25 :(2^(k+2))^5%25=(2^5)^(k+2)%25 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 5,Nat.pow_mul]
  have hbase25 :(2^5)^(k+2)%25=7^(k+2)%25 := by rw [Nat.pow_mod,h2_5]
  have h7pow :7^(k+2)%25=24 := by
    rw [h19_5] at hleft25
    rw [hrewrite25,hbase25] at hleft25
    exact hleft25
  have h7period :7^4%25=1 := by decide
  have h7red :7^(k+2)%25=7^((k+2)%4)%25 := by
    calc
      7^(k+2)%25=7^((k+2)%4+4*((k+2)/4))%25 := by rw [Nat.mod_add_div (k+2) 4]
      _ =7^((k+2)%4)%25 :=
        pow_mod_progression_base 25 7 ((k+2)%4) 4 ((k+2)/4) (by omega) h7period
  have hmod4_2 :(k+2)%4=2 := by
    by_cases h0:(k+2)%4=0
    · rw [h7red,h0] at h7pow
      simp at h7pow
    by_cases h1:(k+2)%4=1
    · rw [h7red,h1] at h7pow
      simp at h7pow
    by_cases h3:(k+2)%4=3
    · rw [h7red,h3] at h7pow
      have h7cube :7^3%25=18 := by decide
      rw [h7cube] at h7pow
      omega
    have hlt :(k+2)%4<4 := Nat.mod_lt _ (by decide)
    omega
  have h2_8893 :2^8893%35573=30394 := by decide
  have h69_8893 :69^8893%35573=1 := by decide
  have h30394_2 :30394^2%35573=35572 := by decide
  have h30394_3 :30394^3%35573=5179 := by decide
  have h30394_4 :30394^4%35573=1 := by decide
  have hleft :(2^(k+2))^8893%35573=69^8893%35573 := by rw [Nat.pow_mod,h35573pow]
  have hrewrite :(2^(k+2))^8893%35573=(2^8893)^(k+2)%35573 := by
    rw [←Nat.pow_mul,Nat.mul_comm (k+2) 8893,Nat.pow_mul]
  have hbase :(2^8893)^(k+2)%35573=30394^(k+2)%35573 := by rw [Nat.pow_mod,h2_8893]
  have h30394pow :30394^(k+2)%35573=1 := by
    rw [h69_8893] at hleft
    rw [hrewrite,hbase] at hleft
    exact hleft
  have h30394red :30394^(k+2)%35573=30394^((k+2)%4)%35573 := by
    calc
      30394^(k+2)%35573=30394^((k+2)%4+4*((k+2)/4))%35573 := by rw [Nat.mod_add_div (k+2) 4]
      _ =30394^((k+2)%4)%35573 :=
        pow_mod_progression_base 35573 30394 ((k+2)%4) 4 ((k+2)/4) (by omega) h30394_4
  have hmod4_0 :(k+2)%4=0 := by
    by_cases h0:(k+2)%4=0
    · exact h0
    by_cases h1:(k+2)%4=1
    · rw [h30394red,h1] at h30394pow
      simp at h30394pow
    by_cases h2:(k+2)%4=2
    · rw [h30394red,h2,h30394_2] at h30394pow
      omega
    have h3:(k+2)%4=3 := by
      have hlt :(k+2)%4<4 := Nat.mod_lt _ (by decide)
      omega
    rw [h30394red,h3,h30394_3] at h30394pow
    omega
  omega

#print axioms no_36_terminal_feeder

#print axioms no_28_terminal_feeder
#print axioms no_35_terminal_feeder

#print axioms no_18_terminal_feeder

end BB6.Agent48.SpaceNeedleObstructionFamilies

import CancellationTopStrip
import Lean.Elab.Tactic.Omega

namespace CancellationThree
open CancellationNat CancellationGap

private theorem pow_mod_congr (a b n : Nat) (h : a%19=b%19) :
    (a^n)%19=(b^n)%19 := by
  calc
    (a^n)%19 = ((a%19)^n)%19 := Nat.pow_mod a n 19
    _ = ((b%19)^n)%19 := by rw [h]
    _ = (b^n)%19 := (Nat.pow_mod b n 19).symm

private theorem power_cycle (a period n : Nat)
    (h : (a^period)%19=1) :
    (a^(period*n))%19=1 := by
  rw [Nat.pow_mul, Nat.pow_mod, h]
  simp

private theorem pow_period (a period n : Nat)
    (h : (a^period)%19=1) :
    (a^n)%19=(a^(n%period))%19 := by
  have he : period*(n/period)+n%period=n := by
    have hh := Nat.mod_add_div n period
    omega
  calc
    (a^n)%19 = (a^(period*(n/period)+n%period))%19 := by rw [he]
    _ = (a^(n%period))%19 := by
      rw [Nat.pow_add, Nat.mul_mod, power_cycle a period (n/period) h]
      omega

private theorem nine_mod36 (r : Nat) : (9^(r+1))%36=9 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem valuation_mod18 (r : Nat) (hr : 1≤r) :
    (valuationA r)%18=7 := by
  have hn : (9^r)%36=9 := by
    have h := nine_mod36 (r-1)
    have he : (r-1)+1=r := by omega
    simpa only [he] using h
  unfold valuationA
  omega

private theorem two_pow_mod19 (r : Nat) (hr : 1≤r) :
    (2^(valuationA r))%19=14 := by
  have hv := valuation_mod18 r hr
  have hc := pow_period 2 18 (valuationA r) (by decide)
  rw [hv] at hc
  exact hc.trans (by decide)

private theorem pow_six_mod19 (r : Nat) :
    (6^r)%19=(6^(r%9))%19 :=
  pow_period 6 9 r (by decide)

private theorem pow_nine_mod19 (r : Nat) :
    (9^r)%19=(9^(r%9))%19 :=
  pow_period 9 9 r (by decide)

/-- Valuation three is an algebraically legal inverse of the cancellation feeder
    precisely on the class r = 7 modulo 9. -/
theorem val_three_iff (r : Nat) (hr : 1≤r) :
    (19 ∣ ((2^(valuationA r))*P (2^(valuationA r)) r+3-2*3)) ↔ r%9=7 := by
  let A := 2^(valuationA r)
  let Q := P A r
  have hA : A%19=14 := two_pow_mod19 r hr
  have hA3 : 3≤A := by
    have hpow : 3≤valuationA r := by
      have hn : 9≤9^r := by
        have ha : (9:Nat)^1≤9^r := Nat.pow_le_pow_right (by decide) hr
        simpa using ha
      dsimp [valuationA]; omega
    have ha : (2:Nat)^3≤2^(valuationA r) := Nat.pow_le_pow_right (by decide) hpow
    dsimp [A]; omega
  have heq := CancellationNat.exact A r hA3
  have hSquare : (A*A)%19=6 := by
    rw [Nat.mul_mod,hA]
  have hPow : (A^(2*r))%19=(6^r)%19 := by
    calc
      (A^(2*r))%19 = ((A*A)^r)%19 := by
        rw [Nat.pow_mul]
        simp only [Nat.pow_succ]
        simp
      _ = (6^r)%19 := pow_mod_congr (A*A) 6 r hSquare
  have heqmod : (17*(Q%19)+(9^r)%19)%19=(6^r)%19 := by
    have hm : ((A+3)*Q)%19=(17*(Q%19))%19 := by
      rw [Nat.mul_mod, show (A+3)%19=17 by omega]
    have hs : ((A+3)*Q+9^r)%19 = (17*(Q%19)+(9^r)%19)%19 := by
      rw [Nat.add_mod,hm, Nat.mod_add_mod]
    rw [←hs,heq,hPow]
  have hQ : 0<Q := by
    cases r with
    | zero => omega
    | succ s =>
      change 0 < A*A*P A s+9^s*(A-3)
      have h9 : 0<9^s := Nat.pow_pos (by decide)
      have hm : 0<A-3 := by omega
      have hprod : 0<9^s*(A-3) := Nat.mul_pos h9 hm
      omega
  have hProd : 6≤A*Q := by
    have hh : A≤A*Q := by exact Nat.le_mul_of_pos_right A hQ
    omega
  have hTarget : (19 ∣ (A*Q+3-6)) ↔ (14*(Q%19))%19=3 := by
    have hrem : (A*Q)%19=(14*(Q%19))%19 := by
      rw [Nat.mul_mod,hA]
    have hsub : (A*Q+3-6)+3=A*Q := by omega
    have hcore : (A*Q+3-6)%19=0 ↔ (A*Q)%19=3 := by omega
    rw [Nat.dvd_iff_mod_eq_zero, hcore,hrem]
  change (19 ∣ (A*Q+3-6)) ↔ r%9=7
  rw [hTarget]
  have hsix := pow_six_mod19 r
  have hnine := pow_nine_mod19 r
  rw [hsix, hnine] at heqmod
  have hQ19 : Q%19<19 := Nat.mod_lt _ (by decide)
  have hr9 : r%9<9 := Nat.mod_lt _ (by decide)
  have htable :
      (List.range 9).all (fun s =>
        (List.range 19).all (fun q =>
          decide (((17*q+(9^s)%19)%19=(6^s)%19) →
            (((14*q)%19=3) ↔ s=7))))=true := by decide
  have hs := (List.all_eq_true.mp htable) (r%9) (List.mem_range.mpr hr9)
  have hq := (List.all_eq_true.mp hs) (Q%19) (List.mem_range.mpr hQ19)
  exact (of_decide_eq_true hq) heqmod

#print axioms val_three_iff
end CancellationThree

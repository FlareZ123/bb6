import Std

namespace CascadePeriodicBeta

/-- Translation by an integer preserves the reduced rational denominator. -/
theorem den_add_int (a : Rat) (z : Int) : (a + (z : Rat)).den = a.den := by
  rw [Rat.den_add]
  simp only [Rat.den_intCast, Rat.num_intCast, Nat.mul_one, Int.natCast_one, Int.mul_one]
  have hg : (a.num + z * (a.den : Int)).natAbs.gcd a.den =
      a.num.natAbs.gcd a.den := by
    change Int.gcd (a.num + z * (a.den : Int)) (a.den : Int) =
      Int.gcd a.num (a.den : Int)
    rw [Int.gcd_add_mul_right_left]
  rw [hg, a.reduced.gcd_eq_one, Nat.div_one]

/-- Multiplication by a natural number cancels exactly its common factors
    with the reduced rational denominator. -/
theorem den_mul_nat (a : Rat) (n : Nat) :
    (a * (n : Rat)).den = a.den / a.den.gcd n := by
  rw [Rat.den_mul]
  simp only [Rat.den_natCast, Rat.num_natCast, Nat.mul_one, Int.natAbs_mul,
    Int.natAbs_natCast]
  rw [Nat.Coprime.gcd_mul_left_cancel n a.reduced, Nat.gcd_comm]

/-- Two rational terms whose sum is integral have equal reduced denominators. -/
theorem den_eq_of_integral_sum (a b : Rat) (z : Int)
    (h : a+b=(z : Rat)) : a.den=b.den := by
  have ha : a = -b + (z : Rat) := by
    calc
      a = (a+b)-b := Rat.add_sub_cancel.symm
      _ = (z : Rat)-b := by rw [h]
      _ = -b + (z : Rat) := by rw [Rat.sub_eq_add_neg, Rat.add_comm]
  rw [ha, den_add_int, Rat.neg_den]

/-- First-difference denominator equality. In the periodic #746 model,
    the exponential coefficient times 2^k and the linear coefficient
    have denominators q and r respectively. -/
theorem first_difference_denominators (alpha beta : Rat) (G D : Nat)
    (z : Int) (h : alpha * ((G-1 : Nat) : Rat) + beta * (D : Rat) = (z : Rat)) :
    alpha.den / alpha.den.gcd (G-1) = beta.den / beta.den.gcd D := by
  have he := den_eq_of_integral_sum _ _ z h
  simpa only [den_mul_nat] using he

/-- Cancelling the common part of a denominator and a multiplier is
    equivalent to the original divisibility condition. -/
theorem quotient_gcd_dvd_iff (q m x : Nat) (hq : 0 < q) :
    q / q.gcd m ∣ x ↔ q ∣ m*x := by
  let d := q.gcd m
  have hd : 0 < d := Nat.gcd_pos_of_pos_left m hq
  have hq' : d * (q/d) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q m)
  have hm' : d * (m/d) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right q m)
  have hc : Nat.Coprime (q/d) (m/d) := Nat.coprime_div_gcd_div_gcd hd
  change q/d ∣ x ↔ q ∣ m*x
  constructor
  · intro h
    have h1 : q ∣ d*x := (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q m) hd).mp h
    exact Nat.dvd_trans h1 (Nat.mul_dvd_mul_right (Nat.gcd_dvd_right q m) x)
  · intro h
    have h1 : d*(q/d) ∣ d*((m/d)*x) := by
      rw [hq', ← Nat.mul_assoc, hm']
      exact h
    exact hc.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hd).mp h1)

/-- Monotonicity of reduced denominators under divisibility. -/
theorem quotient_gcd_dvd_of_dvd (q g m : Nat) (hq : 0 < q) (hg : 0 < g)
    (h : q ∣ g) : q/q.gcd m ∣ g/g.gcd m := by
  apply (quotient_gcd_dvd_iff q m _ hq).mpr
  exact Nat.dvd_trans h ((quotient_gcd_dvd_iff g m _ hg).mp (Nat.dvd_refl _))

/-- If q is a slope denominator dividing a gcd-cap g, equality of the
    first-difference denominators bounds the linear-coordinate denominator. -/
theorem beta_cap (q r g m D T : Nat) (hq : 0 < q) (hr : 0 < r) (hg : 0 < g)
    (h : q ∣ g) (hT : r ∣ T)
    (he : q/q.gcd m = r/r.gcd D) :
    r ∣ T.gcd (D*(g/g.gcd m)) := by
  apply Nat.dvd_gcd hT
  apply (quotient_gcd_dvd_iff r D _ hr).mp
  rw [← he]
  exact quotient_gcd_dvd_of_dvd q g m hq hg h

#print axioms quotient_gcd_dvd_iff
#print axioms quotient_gcd_dvd_of_dvd
#print axioms beta_cap
#print axioms den_add_int
#print axioms den_mul_nat
#print axioms den_eq_of_integral_sum
#print axioms first_difference_denominators

end CascadePeriodicBeta

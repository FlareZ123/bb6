import Mathlib

namespace SheepHensel

/-- The coefficient obtained by cubing a principal 3-adic unit. -/
def cubeCoeff (m q : Nat) : Nat :=
  q + 3^m * q^2 + 3^(2*m-1) * q^3

theorem cubeCoeff_mod_three (m q : Nat) (hm : 1 ≤ m) :
    cubeCoeff m q % 3 = q % 3 := by
  have h1 : 3 ∣ 3^m * q^2 := by
    refine ⟨3^(m-1) * q^2, ?_⟩
    rw [show m = (m-1)+1 by omega, pow_succ]
    ring
  have h2 : 3 ∣ 3^(2*m-1) * q^3 := by
    refine ⟨3^(2*m-2) * q^3, ?_⟩
    rw [show 2*m-1 = (2*m-2)+1 by omega, pow_succ]
    ring
  have h1m : (3^m * q^2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h1
  have h2m : (3^(2*m-1) * q^3) % 3 = 0 := Nat.mod_eq_zero_of_dvd h2
  simp [cubeCoeff, Nat.add_mod, h1m, h2m]

/-- Exact one-step LTE: cubing raises the 3-adic valuation by one
    and preserves the normalized unit modulo 3. -/
theorem cube_lift (m q : Nat) (hm : 1 ≤ m) :
    (1 + 3^m*q)^3 = 1 + 3^(m+1) * cubeCoeff m q := by
  have h1 : 3^(m+1) = 3 * 3^m := by
    rw [pow_succ]
    ring
  have h2 : 3^(2*m+1) = 3^(m+1) * 3^m := by
    rw [← pow_add]
    congr 1
    omega
  have h3 : 3^(3*m) = 3^(m+1) * 3^(2*m-1) := by
    rw [← pow_add]
    congr 1
    omega
  have hsq : 3 * (3^m*q)^2 = 3^(2*m+1) * q^2 := by
    calc
      3 * (3^m*q)^2 = (3 * 3^m * 3^m) * q^2 := by ring
      _ = (3^(m+1) * 3^m) * q^2 := by rw [h1]
      _ = 3^(2*m+1) * q^2 := by rw [← h2]
  have hcube : (3^m*q)^3 = 3^(3*m) * q^3 := by
    calc
      (3^m*q)^3 = (3^m)^3 * q^3 := by ring
      _ = 3^(m*3) * q^3 := by rw [pow_mul]
      _ = 3^(3*m) * q^3 := by congr 2 <;> omega
  calc
    (1 + 3^m*q)^3 =
        1 + 3*(3^m*q) + 3*(3^m*q)^2 + (3^m*q)^3 := by ring
    _ = 1 + 3^(m+1)*q + 3^(2*m+1)*q^2 + 3^(3*m)*q^3 := by
      rw [h1, hsq, hcube]
      ring
    _ = 1 + 3^(m+1) * cubeCoeff m q := by
      rw [cubeCoeff, h2, h3]
      ring

/-- For every n, 2^(2*3^n) is 1 modulo 3^(n+1), with a normalized
    quotient that is a 3-adic unit. This is the elementary LTE induction. -/
theorem two_lte (n : Nat) :
    ∃ q : Nat, 2^(2*3^n) = 1 + 3^(n+1)*q ∧ q % 3 = 1 := by
  induction n with
  | zero =>
      exact ⟨1, by norm_num, by norm_num⟩
  | succ n ih =>
      obtain ⟨q, hpow, hq⟩ := ih
      refine ⟨cubeCoeff (n+1) q, ?_, ?_⟩
      · have hexp : 2*3^(n+1) = (2*3^n)*3 := by
          rw [pow_succ]
          ring
        calc
          2^(2*3^(n+1)) = (2^(2*3^n))^3 := by rw [hexp, pow_mul]
          _ = (1 + 3^(n+1)*q)^3 := by rw [hpow]
          _ = 1 + 3^(n+2)*cubeCoeff (n+1) q := by
            simpa using cube_lift (n+1) q (by omega)
      · rw [cubeCoeff_mod_three (n+1) q (by omega)]
        exact hq

/-- Raising a number congruent to one modulo 3^m preserves that congruence. -/
theorem pow_preserves_modulus (m q n : Nat) :
    ∃ r : Nat, (1 + 3^m*q)^n = 1 + 3^m*r := by
  induction n with
  | zero =>
      exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r + q + 3^m*r*q, ?_⟩
      rw [pow_succ, hr]
      ring

/-- The particular multiplier 2^1102248 is 1+3^10 times a 3-adic unit.
    Here 1102248 = 28*(2*3^9); the exponent 28 is 1 modulo 3. -/
theorem two_delta_unit :
    ∃ q : Nat, 2^1102248 = 1 + 3^10*q ∧ q % 3 = 1 := by
  obtain ⟨q, hb, hq⟩ := two_lte 9
  let b := 2^(2*3^9)
  have hb' : b = 1 + 3^10*q := by simpa [b] using hb
  have hc : b^3 = 1 + 3^11*cubeCoeff 10 q := by
    calc
      b^3 = (1 + 3^10*q)^3 := by rw [hb']
      _ = 1 + 3^11*cubeCoeff 10 q := by
        simpa using cube_lift 10 q (by norm_num)
  obtain ⟨r, hr⟩ := pow_preserves_modulus 11 (cubeCoeff 10 q) 9
  have h27 : b^27 = 1 + 3^11*r := by
    calc
      b^27 = (b^3)^9 := by rw [show 27 = 3*9 by norm_num, pow_mul]
      _ = (1 + 3^11*cubeCoeff 10 q)^9 := by rw [hc]
      _ = 1 + 3^11*r := hr
  have hexp : 1102248 = (2*3^9)*28 := by norm_num
  have hb28 : 2^1102248 = b^28 := by
    dsimp [b]
    rw [hexp, pow_mul]
  let q0 := q + 3*r + 3^11*r*q
  refine ⟨q0, ?_, ?_⟩
  · calc
      2^1102248 = b^28 := hb28
      _ = b^27*b := by rw [show 28 = 27+1 by norm_num, pow_succ]
      _ = (1 + 3^11*r)*(1 + 3^10*q) := by rw [h27, hb']
      _ = 1 + 3^10*q0 := by ring
  · simp [q0, Nat.add_mod, Nat.mul_mod, hq]

/-- The unit property of 2^1102248 persists at every 3-adic lift level. -/
theorem unit_lift (g q0 : Nat)
    (hbase : g = 1 + 3^10*q0) (hq0 : q0 % 3 = 1) :
    ∀ t : Nat, ∃ q : Nat,
      g^(3^t) = 1 + 3^(10+t)*q ∧ q % 3 = 1 := by
  intro t
  induction t with
  | zero =>
      exact ⟨q0, by simpa [hbase], hq0⟩
  | succ t ih =>
      obtain ⟨q, hpow, hq⟩ := ih
      refine ⟨cubeCoeff (10+t) q, ?_, ?_⟩
      · have hexp : 3^(t+1) = 3^t*3 := by
          rw [pow_succ]
          ring
        calc
          g^(3^(t+1)) = (g^(3^t))^3 := by rw [hexp, pow_mul]
          _ = (1 + 3^(10+t)*q)^3 := by rw [hpow]
          _ = 1 + 3^(11+t)*cubeCoeff (10+t) q := by
            simpa [Nat.add_assoc] using cube_lift (10+t) q (by omega)
      · rw [cubeCoeff_mod_three (10+t) q (by omega)]
        exact hq

private theorem pow_mod_three (g k : Nat) (hg : g % 3 = 1) :
    g^k % 3 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      simp [ih, hg]

private theorem choose_digit (b c : Nat) (hc : c % 3 ≠ 0) :
    ∃ u : Nat, u < 3 ∧ 3 ∣ b + c*u := by
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hcc : c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hb with hb0 | hb1 | hb2
  · rcases hcc with hc1 | hc2
    · refine ⟨0, by omega, ?_⟩
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.mul_mod, hb0, hc1]
    · refine ⟨0, by omega, ?_⟩
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.mul_mod, hb0, hc2]
  · rcases hcc with hc1 | hc2
    · refine ⟨2, by omega, ?_⟩
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.mul_mod, hb1, hc1]
    · refine ⟨1, by omega, ?_⟩
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.mul_mod, hb1, hc2]
  · rcases hcc with hc1 | hc2
    · refine ⟨1, by omega, ?_⟩
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.mul_mod, hb2, hc1]
    · refine ⟨2, by omega, ?_⟩
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.mul_mod, hb2, hc2]

/-- One Hensel digit: if the current numerator vanishes modulo 3^m,
    exactly one of k, k+3^t, k+2*3^t vanishes modulo 3^(m+1). -/
private theorem lift_step {m t A g C k q b u : Nat}
    (hm : 1 ≤ m)
    (hbase : A*g^k + C = 3^m*b)
    (hpow : g^(3^t) = 1 + 3^m*q)
    (hu : u < 3)
    (hdiv : 3 ∣ b + A*g^k*q*u) :
    3^(m+1) ∣ A*g^(k+u*3^t) + C := by
  interval_cases u
  · have hb : 3 ∣ b := by simpa using hdiv
    obtain ⟨r, hr⟩ := hb
    refine ⟨r, ?_⟩
    rw [show k + 0*3^t = k by omega,
        show 3^(m+1) = 3^m*3 by rw [pow_succ]]
    rw [hbase, hr]
    ring
  · have hmul : g^(k+3^t) = g^k*g^(3^t) := by rw [pow_add]
    have hfactor : A*g^(k+3^t)+C = 3^m*(b+A*g^k*q) := by
      rw [hmul, hpow]
      calc
        A*(g^k*(1+3^m*q))+C = (A*g^k)*(1+3^m*q)+C := by ring
        _ = (A*g^k+C) + 3^m*(A*g^k*q) := by ring
        _ = 3^m*(b+A*g^k*q) := by rw [hbase]; ring
    have hdiv' : 3 ∣ b+A*g^k*q := by simpa using hdiv
    obtain ⟨r, hr⟩ := hdiv'
    refine ⟨r, ?_⟩
    rw [hfactor, hr, pow_succ]
    ring
  · have hmul : g^(k+2*3^t) = g^k*(g^(3^t))^2 := by
      rw [pow_add]
      rw [show 2*3^t = 3^t+3^t by omega, pow_add]
    have hfactor :
        A*g^(k+2*3^t)+C =
          3^m*(b+2*A*g^k*q) + A*g^k*3^(2*m)*q^2 := by
      rw [hmul, hpow]
      have hsquare : (1+3^m*q)^2 = 1+2*3^m*q+3^(2*m)*q^2 := by ring
      rw [hsquare]
      calc
        A*(g^k*(1+2*3^m*q+3^(2*m)*q^2))+C =
            (A*g^k)*(1+2*3^m*q+3^(2*m)*q^2)+C := by ring
        _ = (A*g^k+C) + 3^m*(2*A*g^k*q) + A*g^k*3^(2*m)*q^2 := by ring
        _ = 3^m*(b+2*A*g^k*q) + A*g^k*3^(2*m)*q^2 := by rw [hbase]; ring
    have hdiv' : 3 ∣ b+2*A*g^k*q := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdiv
    have hmain : 3^(m+1) ∣ 3^m*(b+2*A*g^k*q) := by
      obtain ⟨r, hr⟩ := hdiv'
      refine ⟨r, ?_⟩
      rw [hr, pow_succ]
      ring
    have hexp : 3^(2*m) = 3^(m+1)*3^(m-1) := by
      rw [← pow_add]
      congr 1
      omega
    have hextra : 3^(m+1) ∣ A*g^k*3^(2*m)*q^2 := by
      refine ⟨A*g^k*3^(m-1)*q^2, ?_⟩
      rw [hexp]
      ring
    rw [hfactor]
    exact Nat.dvd_add hmain hextra

/-- General 3-adic Hensel lifting for A*g^k+C, with a unit first-order
    multiplier. The unique digit at each level is constructive. -/
theorem hensel_lift (A g C : Nat)
    (hA : A % 3 ≠ 0)
    (hg : g % 3 = 1)
    (hbase : 3^10 ∣ A+C)
    (hunit : ∀ t : Nat, ∃ q : Nat,
      g^(3^t) = 1 + 3^(10+t)*q ∧ q % 3 = 1) :
    ∀ t : Nat, ∃ k : Nat, 3^(10+t) ∣ A*g^k+C := by
  intro t
  induction t with
  | zero =>
      simpa using hbase
  | succ t ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨q, hqpow, hq⟩ := hunit t
      obtain ⟨b, hb⟩ := hk
      have hgk : g^k % 3 = 1 := pow_mod_three g k hg
      have hcoeff : (A*g^k*q)%3 = A%3 := by
        simp [Nat.mul_mod, hgk, hq]
      have hcoeffUnit : (A*g^k*q)%3 ≠ 0 := by
        rw [hcoeff]
        exact hA
      obtain ⟨u, hu, hdiv⟩ := choose_digit b (A*g^k*q) hcoeffUnit
      refine ⟨k+u*3^t, ?_⟩
      have hstep := lift_step (m:=10+t) (t:=t) (A:=A) (g:=g) (C:=C)
        (k:=k) (q:=q) (b:=b) (u:=u) (by omega) hb hqpow hu hdiv
      simpa [Nat.add_assoc] using hstep

end SheepHensel

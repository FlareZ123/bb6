import Std

namespace BB6.Agent44

/-- Uniform gap certificate for the rectangular range of P1 power-leaf
coefficients. Here t=7X-u, and every variable is an integer. -/
theorem universal_power_band (u X t A C : Int)
    (hu : 1 ≤ u) (hX : 32*u ≤ X) (ht : t+u=7*X)
    (hAlo : 65832≤A) (hAhi : A≤130896)
    (hClo : 8≤C) (hChi : C≤130290) :
    458752*X < A*t+C ∧ A*t+C < 917504*X := by
  have htnonneg : 0 ≤ t := by omega
  have hLo : 65832*t ≤ A*t :=
    Int.mul_le_mul_of_nonneg_right hAlo htnonneg
  have hHi : A*t ≤ 130896*t :=
    Int.mul_le_mul_of_nonneg_right hAhi htnonneg
  omega

/-- The interval between successive 14-powers contains no 14-power. -/
theorem between_int_14_powers_no_hit (N j : Nat) (y : Int)
    (hlo : (14:Int) * 2^(N+15) < y)
    (hhi : y < (14:Int) * 2^(N+16)) :
    y ≠ (14:Int) * 2^j := by
  intro heq
  by_cases h : j ≤ N+15
  · have hp : (2:Nat)^j ≤ (2:Nat)^(N+15) :=
      Nat.pow_le_pow_right (by omega) h
    have hz : (2:Int)^j ≤ (2:Int)^(N+15) := by
      exact_mod_cast hp
    omega
  · have hh : N+16 ≤ j := by omega
    have hp : (2:Nat)^(N+16) ≤ (2:Nat)^j :=
      Nat.pow_le_pow_right (by omega) hh
    have hz : (2:Int)^(N+16) ≤ (2:Int)^j := by
      exact_mod_cast hp
    omega

/-- Every affine expression in the coefficient rectangle avoids 14-powers
whenever the parameter has the stipulated exponential growth. -/
theorem universal_no_14_power (N j : Nat) (u t A C : Int)
    (hu : 1 ≤ u)
    (hX : 32*u ≤ (2:Int)^N)
    (ht : t+u=7*(2:Int)^N)
    (hAlo : 65832≤A) (hAhi : A≤130896)
    (hClo : 8≤C) (hChi : C≤130290) :
    A*t+C ≠ (14:Int)*2^j := by
  obtain ⟨hlo,hhi⟩ := universal_power_band u ((2:Int)^N) t A C
    hu hX ht hAlo hAhi hClo hChi
  have hLowEq : (14:Int) * 2^(N+15) = 458752*2^N := by
    simp [Int.pow_add, show (2:Int)^15 = 32768 by decide, Int.mul_comm, Int.mul_left_comm]
  have hHighEq : (14:Int) * 2^(N+16) = 917504*2^N := by
    simp [Int.pow_add, show (2:Int)^16 = 65536 by decide, Int.mul_comm, Int.mul_left_comm]
  apply between_int_14_powers_no_hit N j (A*t+C)
  · simpa only [hLowEq] using hlo
  · simpa only [hHighEq] using hhi

/-- Nat-facing wrapper for the original even_left_power_shape gate. -/
theorem universal_nat_no_power (N x : Nat) (u t A C : Int)
    (hu : 1 ≤ u) (hX : 32*u ≤ (2:Int)^N)
    (ht : t+u=7*(2:Int)^N)
    (hAlo : 65832≤A) (hAhi : A≤130896)
    (hClo : 8≤C) (hChi : C≤130290)
    (hx : ((x+12:Nat):Int) = A*t+C) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  intro j hj
  have h := universal_no_14_power N j u t A C
    hu hX ht hAlo hAhi hClo hChi
  have hc : ((x+12:Nat):Int) = ((14*2^j:Nat):Int) :=
    congrArg Int.ofNat hj
  rw [hx] at hc
  apply h
  simpa using hc

/-- Elementary exponential growth estimate. -/
theorem two_pow_dominates (q : Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.pow_succ]
    omega

theorem universal_exponent_growth (q R : Nat) (hR : 21≤R) :
    32*(q+1) ≤ 2^(65536*q+R-16) := by
  have hq : q ≤ 65536*q+(R-21) := by omega
  have hp : (2:Nat)^q ≤ (2:Nat)^(65536*q+(R-21)) :=
    Nat.pow_le_pow_right (by omega) hq
  have hbase := two_pow_dominates q
  have hExp : 65536*q+R-16 = (65536*q+(R-21))+5 := by omega
  rw [hExp, Nat.pow_add]
  have hFive : (2:Nat)^5=32 := by decide
  rw [hFive]
  omega

/-- P1 affine leaf exclusion for any critical residue R at least 21. -/
theorem p1_affine_leaf_no_power
    (q R x : Nat) (A C : Int) (hR : 21≤R)
    (hAlo : 65832≤A) (hAhi : A≤130896)
    (hClo : 8≤C) (hChi : C≤130290)
    (hx : ((x+12:Nat):Int) =
      A*((7*(2^(65536*q+R-16)):Nat)-(q+1):Nat)+C) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  let N := 65536*q+R-16
  let X := (2:Nat)^N
  let t := 7*X-(q+1)
  have hg : 32*(q+1) ≤ X := universal_exponent_growth q R hR
  have hsub : q+1 ≤ 7*X := by omega
  have htNat : t+(q+1)=7*X := Nat.sub_add_cancel hsub
  have htInt : (t:Int)+(q+1:Int)=7*(2:Int)^N := by
    exact_mod_cast htNat
  have hXInt : 32*(q+1:Int) ≤ (2:Int)^N := by
    exact_mod_cast hg
  have hu : (1:Int) ≤ q+1 := by omega
  exact universal_nat_no_power N x (q+1) t A C hu hXInt htInt
    hAlo hAhi hClo hChi hx

#print axioms BB6.Agent44.universal_power_band
#print axioms BB6.Agent44.between_int_14_powers_no_hit
#print axioms BB6.Agent44.universal_no_14_power
#print axioms BB6.Agent44.universal_nat_no_power
#print axioms BB6.Agent44.universal_exponent_growth
#print axioms BB6.Agent44.p1_affine_leaf_no_power
end BB6.Agent44

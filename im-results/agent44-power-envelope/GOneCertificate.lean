import Std

set_option maxRecDepth 4096

namespace BB6.Agent44

/-- Low shifted-coordinate coefficient rectangle: strictly between powers
2^(N+18) and 2^(N+19) when X=2^N. -/
theorem lower_shifted_band (u X t A C : Int)
    (hu : 1 ≤ u) (hX : 16384*u ≤ X) (ht : t+u=7*X)
    (hAlo : 65536≤A) (hAhi : A≤74888)
    (hClo : 12≤C) (hChi : C≤74562) :
    262144*X < A*t+C ∧ A*t+C < 524288*X := by
  have htpos : 0 ≤ t := by omega
  have hlo : 65536*t ≤ A*t :=
    Int.mul_le_mul_of_nonneg_right hAlo htpos
  have hhi : A*t ≤ 74888*t :=
    Int.mul_le_mul_of_nonneg_right hAhi htpos
  omega

/-- High shifted-coordinate coefficient rectangle: next consecutive band. -/
theorem upper_shifted_band (u X t A C : Int)
    (hu : 1 ≤ u) (hX : 16384*u ≤ X) (ht : t+u=7*X)
    (hAlo : 74928≤A) (hAhi : A≤130720)
    (hClo : 10≤C) (hChi : C≤130036) :
    524288*X < A*t+C ∧ A*t+C < 1048576*X := by
  have htpos : 0 ≤ t := by omega
  have hlo : 74928*t ≤ A*t :=
    Int.mul_le_mul_of_nonneg_right hAlo htpos
  have hhi : A*t ≤ 130720*t :=
    Int.mul_le_mul_of_nonneg_right hAhi htpos
  omega

/-- A positive integer strictly between consecutive powers of two cannot
be a pure power of two. -/
theorem two_power_gap (N j e : Nat) (y : Int)
    (hlo : (2:Int)^(N+e) < y)
    (hhi : y < (2:Int)^(N+e+1)) :
    y ≠ (2:Int)^j := by
  intro hj
  by_cases h : j ≤ N+e
  · have hp : (2:Nat)^j ≤ (2:Nat)^(N+e) :=
      Nat.pow_le_pow_right (by omega) h
    have hz : (2:Int)^j ≤ (2:Int)^(N+e) := by exact_mod_cast hp
    omega
  · have hge : N+e+1 ≤ j := by omega
    have hp : (2:Nat)^(N+e+1) ≤ (2:Nat)^j :=
      Nat.pow_le_pow_right (by omega) hge
    have hz : (2:Int)^(N+e+1) ≤ (2:Int)^j := by exact_mod_cast hp
    omega

/-- A uniform pure-two-power obstruction for the candidate inverse cones. -/
theorem shifted_no_power (N j : Nat) (u t A C : Int)
    (hu : 1 ≤ u) (hX : 16384*u ≤ (2:Int)^N)
    (ht : t+u=7*(2:Int)^N)
    (hcase : (65536≤A ∧ A≤74888 ∧ 12≤C ∧ C≤74562) ∨
             (74928≤A ∧ A≤130720 ∧ 10≤C ∧ C≤130036)) :
    A*t+C ≠ (2:Int)^j := by
  rcases hcase with hlow | hhigh
  · obtain ⟨hlo, hhi⟩ := lower_shifted_band u ((2:Int)^N) t A C
      hu hX ht hlow.1 hlow.2.1 hlow.2.2.1 hlow.2.2.2
    have hl : (2:Int)^(N+18) = 262144*2^N := by
      simp [Int.pow_add, show (2:Int)^18 = 262144 by decide, Int.mul_comm]
    have hh : (2:Int)^(N+18+1) = 524288*2^N := by
      have he : N+18+1=N+19 := by omega
      rw [he]
      simp [Int.pow_add, show (2:Int)^19 = 524288 by decide, Int.mul_comm]
    exact two_power_gap N j 18 (A*t+C) (by simpa only [hl] using hlo)
      (by simpa only [hh] using hhi)
  · obtain ⟨hlo, hhi⟩ := upper_shifted_band u ((2:Int)^N) t A C
      hu hX ht hhigh.1 hhigh.2.1 hhigh.2.2.1 hhigh.2.2.2
    have hl : (2:Int)^(N+19) = 524288*2^N := by
      simp [Int.pow_add, show (2:Int)^19 = 524288 by decide, Int.mul_comm]
    have hh : (2:Int)^(N+19+1) = 1048576*2^N := by
      have he : N+19+1=N+20 := by omega
      rw [he]
      simp [Int.pow_add, show (2:Int)^20 = 1048576 by decide, Int.mul_comm]
    exact two_power_gap N j 19 (A*t+C) (by simpa only [hl] using hlo)
      (by simpa only [hh] using hhi)

/-- Elementary exponential growth estimate. -/
theorem two_pow_dominates (q : Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero => decide
  | succ q ih => rw [Nat.pow_succ]; omega

/-- Strong growth for critical residues R >= 30, all q. -/
theorem universal_strong_growth (q R : Nat) (hR : 30≤R) :
    16384*(q+1) ≤ 2^(65536*q+R-16) := by
  have hq : q ≤ 65536*q+(R-30) := by omega
  have hp : (2:Nat)^q ≤ (2:Nat)^(65536*q+(R-30)) :=
    Nat.pow_le_pow_right (by omega) hq
  have hbase := two_pow_dominates q
  have hExp : 65536*q+R-16 = (65536*q+(R-30))+14 := by omega
  rw [hExp, Nat.pow_add]
  have hFourteen : (2:Nat)^14=16384 := by decide
  rw [hFourteen]
  omega

/-- Nat-facing generic forbidden-pure-power certificate, automatically proves
the exponent-growth premise from q,R. -/
theorem p1_shifted_leaf_no_power
    (q R D : Nat) (A C : Int) (hR : 30≤R)
    (hcase : (65536≤A ∧ A≤74888 ∧ 12≤C ∧ C≤74562) ∨
             (74928≤A ∧ A≤130720 ∧ 10≤C ∧ C≤130036))
    (hD : (D:Int) =
      A*((7*(2^(65536*q+R-16)):Nat)-(q+1):Nat)+C) :
    ∀ j : Nat, D ≠ 2^j := by
  let N := 65536*q+R-16
  let X := (2:Nat)^N
  let t := 7*X-(q+1)
  have hg : 16384*(q+1) ≤ X := universal_strong_growth q R hR
  have hsub : q+1 ≤ 7*X := by omega
  have htNat : t+(q+1)=7*X := Nat.sub_add_cancel hsub
  have htInt : (t:Int)+(q+1:Int)=7*(2:Int)^N := by
    exact_mod_cast htNat
  have hXInt : 16384*(q+1:Int) ≤ (2:Int)^N := by
    have hc : ((16384*(q+1):Nat):Int) ≤ (X:Int) := Int.ofNat_le.mpr hg
    have hCastMul : ((16384*(q+1):Nat):Int) = 16384*(q+1:Int) := by
      rw [Int.natCast_mul, Int.natCast_add]
      rfl
    have hXCast : (X:Int) = (2:Int)^N := by
      change (((2:Nat)^N):Int) = (2:Int)^N
      exact Int.natCast_pow 2 N
    rw [hCastMul, hXCast] at hc
    exact hc
  have hu : (1:Int) ≤ q+1 := by omega
  intro j hj
  have h := shifted_no_power N j (q+1) t A C hu hXInt htInt hcase
  have hc : (D:Int) = ((2^j:Nat):Int) := congrArg Int.ofNat hj
  rw [hD] at hc
  apply h
  simpa using hc

#print axioms BB6.Agent44.lower_shifted_band
#print axioms BB6.Agent44.upper_shifted_band
#print axioms BB6.Agent44.two_power_gap
#print axioms BB6.Agent44.shifted_no_power
#print axioms BB6.Agent44.universal_strong_growth
#print axioms BB6.Agent44.p1_shifted_leaf_no_power
end BB6.Agent44

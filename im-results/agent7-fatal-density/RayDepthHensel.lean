import SignedRayPeriod
set_option maxHeartbeats 0

namespace CascadeRayDepthHensel
open CascadeRayPeriod

/-- The exact depth stride for divisibility by 3^(k+1). -/
def depthPeriod (k : Nat) : Nat := 2 * 3^k

/-- The unit coefficient in 2^(2*3^k) = 1 + 3^(k+1) * depthCoeff k.
    Cubing the preceding lift preserves the coefficient modulo three. -/
def depthCoeff : Nat → Nat
  | 0 => 1
  | k+1 =>
      depthCoeff k + 3^(k+1)*(depthCoeff k)^2 +
        3^(2*k+1)*(depthCoeff k)^3

theorem depthCoeff_unit (k : Nat) : depthCoeff k % 3 ≠ 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
      simp only [depthCoeff]
      have h1 : (3^(k+1)*depthCoeff k^2)%3=0 := by
        rw [Nat.mul_mod]
        simp [Nat.pow_succ]
      have h2 : (3^(2*k+1)*depthCoeff k^3)%3=0 := by
        rw [show 2*k+1=(2*k)+1 by omega, Nat.pow_succ, Nat.mul_mod]
        simp
      have hsum :
          (depthCoeff k + 3^(k+1)*depthCoeff k^2 +
            3^(2*k+1)*depthCoeff k^3)%3 = depthCoeff k%3 := by
        simp [Nat.add_mod,h1,h2]
      rw [hsum]
      exact ih

/-- All-precision binomial lift of the order of two modulo powers of three. -/
theorem pow_depth_period (k : Nat) :
    2^depthPeriod k = 1 + 3^(k+1)*depthCoeff k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hL :
          depthPeriod (k+1) =
            depthPeriod k + depthPeriod k + depthPeriod k := by
        simp [depthPeriod,Nat.pow_succ]
        omega
      calc
        2^depthPeriod (k+1) =
            2^(depthPeriod k + depthPeriod k + depthPeriod k) := by rw [hL]
        _ = (2^depthPeriod k)*(2^depthPeriod k)*(2^depthPeriod k) := by
          rw [Nat.pow_add,Nat.pow_add]
        _ = (1+3^(k+1)*depthCoeff k)^3 := by
          rw [ih]
          simp [Nat.pow_succ,Nat.mul_assoc]
        _ = 1+3^(k+2)*depthCoeff (k+1) := by
          have hp1 : 3^(k+2)=3^(k+1)*3 := by
            rw [show k+2=(k+1)+1 by omega,Nat.pow_succ]
          have hp2 : 3^(2*k+1)=3^(k+1)*3^k := by
            rw [show 2*k+1=(k+1)+k by omega,Nat.pow_add]
          simp only [depthCoeff]
          rw [hp1,hp2]
          simp [Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,
            Nat.mul_comm,Nat.mul_left_comm]
          omega

/-- The signed ray numerator has period 2*3^k modulo 3^(k+1),
    uniformly in both the fatal index and the depth. -/
theorem signedZ_period (n j k : Nat) :
    signedZ n (j+depthPeriod k)%(3:Int)^(k+1) =
      signedZ n j%(3:Int)^(k+1) := by
  have he : j+depthPeriod k+1=(j+1)+depthPeriod k := by omega
  have hpowNat : (2:Nat)^(j+depthPeriod k+1) =
      (2:Nat)^(j+1)*(2:Nat)^(depthPeriod k) := by
    rw [he,Nat.pow_add]
  have hpowInt : (2:Int)^(j+depthPeriod k+1) =
      (2:Int)^(j+1)*(1+(3:Int)^(k+1)*depthCoeff k) := by
    have hh := congrArg (fun x : Nat => (2:Nat)^(j+1)*x)
      (pow_depth_period k)
    have hn : (2:Nat)^(j+1)*(2:Nat)^(depthPeriod k) =
        (2:Nat)^(j+1)*(1+3^(k+1)*depthCoeff k) := hh
    rw [←hpowNat] at hn
    exact_mod_cast hn
  have hz : signedZ n (j+depthPeriod k) =
      signedZ n j-(3:Int)^(k+1)*
        ((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k) := by
    dsimp [signedZ]
    rw [hpowInt]
    push_cast
    simp [Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    omega
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  apply Int.emod_eq_zero_of_dvd
  refine ⟨-((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k),?_⟩
  rw [hz]
  have hneg :
      -((3:Int)^(k+1)*((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k)) =
        (3:Int)^(k+1)*-((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k) := by
    exact Int.neg_mul_eq_mul_neg _ _
  rw [Int.sub_eq_add_neg,Int.sub_eq_add_neg,hneg]
  omega

/-- Periodicity under every whole number of depth strides. -/
theorem signedZ_period_mul (n j k m : Nat) :
    signedZ n (j+m*depthPeriod k)%(3:Int)^(k+1) =
      signedZ n j%(3:Int)^(k+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx :
          j+(m+1)*depthPeriod k =
            (j+m*depthPeriod k)+depthPeriod k := by
        rw [Nat.succ_mul]
        omega
      rw [hidx]
      rw [signedZ_period n (j+m*depthPeriod k) k]
      exact ih

private theorem pow_two_mod_three (m : Nat) :
    2^m%3 = if m%2=0 then 1 else 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      by_cases hm : m%2=0
      · have hs : (m+1)%2=1 := by omega
        rw [ih,if_pos hm]
        simp [hs]
      · have hs : (m+1)%2=0 := by omega
        rw [ih,if_neg hm]
        simp [hs]

/-- In the surviving fatal-index sectors, 2^n and n have the same
    nonzero residue modulo three. -/
theorem pow_sector_mod_three (n : Nat)
    (hn : n%6=4 ∨ n%6=5) : 2^n%3=n%3 := by
  rcases hn with h|h
  · have h2 : n%2=0 := by omega
    have h3 : n%3=1 := by omega
    rw [pow_two_mod_three,h2]
    simp [h3]
  · have h2 : n%2=1 := by omega
    have h3 : n%3=2 := by omega
    rw [pow_two_mod_three,h2]
    simp [h3]

private theorem signedZ_zero_mod_three (n : Nat)
    (hn : n%6=4 ∨ n%6=5) : signedZ n 0%3=0 := by
  have hp := pow_sector_mod_three n hn
  have hpi : ((2:Int)^n)%3=(n:Int)%3 := by exact_mod_cast hp
  dsimp [signedZ]
  push_cast
  omega

private theorem signedZ_one_mod_three_ne (n : Nat)
    (hn : n%6=4 ∨ n%6=5) : signedZ n 1%3≠0 := by
  have hp := pow_sector_mod_three n hn
  have hpi : ((2:Int)^n)%3=(n:Int)%3 := by exact_mod_cast hp
  dsimp [signedZ]
  push_cast
  omega

/-- The initial mod-three zero occurs exactly at even ray depths. -/
theorem signedZ_mod_three_even_iff (n j : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    signedZ n j%3=0 ↔ j%2=0 := by
  by_cases hj : j%2=0
  · have hsplit : j=2*(j/2) := by omega
    rw [hsplit]
    have hper := signedZ_period_mul n 0 0 (j/2)
    simpa [depthPeriod,Nat.mul_comm] using
      (hper.trans (signedZ_zero_mod_three n hn))
  · have hj1 : j%2=1 := by omega
    have hsplit : j=1+2*(j/2) := by omega
    rw [hsplit]
    have hper0 := signedZ_period_mul n 1 0 (j/2)
    have hper : signedZ n (1+2*(j/2))%3=signedZ n 1%3 := by
      simpa [depthPeriod,Nat.mul_comm] using hper0
    have hone := signedZ_one_mod_three_ne n hn
    constructor
    · intro hz
      have hz1 : signedZ n 1%3=0 := by rw [←hper]; exact hz
      exact False.elim (hone hz1)
    · intro hz
      omega

#print axioms depthCoeff_unit
#print axioms pow_depth_period
#print axioms signedZ_period
#print axioms signedZ_period_mul
#print axioms signedZ_mod_three_even_iff
end CascadeRayDepthHensel

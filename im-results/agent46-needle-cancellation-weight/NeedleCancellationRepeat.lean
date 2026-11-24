import Std

namespace NeedleCancellationRepeat

/-- First-order binomial congruence, including signed bases. -/
theorem linearize (y D : Int) (k : Nat) :
    ∃ z : Int, (y+D)^(k+1) = y^(k+1)+(k+1:Nat)*y^k*D+D*D*z := by
  induction k with
  | zero => exact ⟨0,by simp [Int.pow_succ]⟩
  | succ k ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨z*(y+D)+(k+1:Nat)*y^k,?_⟩
    rw [Int.pow_succ (y+D),hz,Int.pow_succ y (k+1),Int.pow_succ y k]
    push_cast
    grind

/-- The denominator is coprime to 3 for every positive dyadic exponent. -/
theorem denominator_coprime (m : Nat) : (2^m+3).Coprime 3 := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm,Nat.gcd_add_self_right,Nat.gcd_comm]
  exact Nat.Coprime.pow_left m (by decide : (2:Nat).Coprime 3)

/-- If the square of a denominator divides the signed-power cancellation
numerator, that denominator divides the exponent quotient. -/
theorem square_requires_quotient (m k : Nat) (hk : 0<k)
    (h : ((2:Int)^m+3)*((2:Int)^m+3) ∣ ((2:Int)^m)^k-(-3:Int)^k) :
    2^m+3 ∣ k := by
  let D : Int := (2:Int)^m+3
  have hD : D≠0 := by dsimp [D]; have hp : 0<(2:Int)^m := Int.pow_pos (by decide); omega
  obtain ⟨j,rfl⟩ : ∃ j : Nat, k=j+1 := ⟨k-1,by omega⟩
  obtain ⟨z,hz⟩ := linearize (-3) D j
  have hbase : -3+D=(2:Int)^m := by dsimp [D]; omega
  rw [hbase] at hz
  change D*D ∣ ((2:Int)^m)^(j+1)-(-3:Int)^(j+1) at h
  have hd : D*D ∣ D*((j+1:Nat)*(-3:Int)^j) := by
    have hh := Int.dvd_sub h (Int.dvd_mul_right (D*D) z)
    have he : ((2:Int)^m)^(j+1)-(-3:Int)^(j+1)-D*D*z=D*((j+1:Nat)*(-3:Int)^j) := by grind
    rwa [he] at hh
  have hd' : D ∣ (j+1:Nat)*(-3:Int)^j := (Int.mul_dvd_mul_iff_left hD).mp hd
  have hNat := Int.natAbs_dvd_natAbs.mpr hd'
  have hDnat : D.natAbs=2^m+3 := by simp [D,Int.natAbs_add_of_nonneg,Int.pow_nonneg,Int.natAbs_pow]
  rw [hDnat,Int.natAbs_mul,Int.natAbs_pow] at hNat
  change 2^m+3 ∣ (j+1)*3^j at hNat
  exact ((denominator_coprime m).pow_right j).dvd_of_dvd_mul_right hNat

/-- If m already occurred in a reverse history, the current denominator
product L contains D=2^m+3. A new legal exceptional cancellation at m
then forces D to divide k=n/m. -/
theorem repeated_parameter_requires_quotient (n L m : Nat) (d : Int)
    (hn : 0<n) (_hm : 0<m) (hdiv : n%m=0) (hprev : 2^m+3 ∣ L)
    (hcan : d+(L:Int)*(5-2*(m:Int))= -(-3:Int)^(n/m))
    (hlegal : (L:Int)*((2:Int)^m+3) ∣ (2:Int)^n+d+(L:Int)*(5-2*(m:Int))) :
    2^m+3 ∣ n/m := by
  have he : m*(n/m)=n := by have hh:=Nat.div_add_mod n m; omega
  have hk : 0<n/m := by
    by_cases hz : n/m=0
    · rw [hz,Nat.mul_zero] at he; omega
    · exact Nat.pos_of_ne_zero hz
  have hprevI : (2:Int)^m+3 ∣ (L:Int) := by exact_mod_cast hprev
  have hd : ((2:Int)^m+3)*((2:Int)^m+3) ∣ (L:Int)*((2:Int)^m+3) := by
    obtain ⟨a,ha⟩ := hprevI
    exact ⟨a,by rw [ha]; ac_rfl⟩
  have hh := Int.dvd_trans hd hlegal
  have hN : (2:Int)^n=((2:Int)^m)^(n/m) := by rw [←Int.pow_mul,he]
  have hnum : (2:Int)^n+d+(L:Int)*(5-2*(m:Int))=((2:Int)^m)^(n/m)-(-3:Int)^(n/m) := by omega
  rw [hnum] at hh
  exact square_requires_quotient m (n/m) hk hh

/-- A repeated parameter with a too-large denominator cannot be the
exceptional cancellation candidate at a legal inverse node. -/
theorem repeated_parameter_exclusion (n L m : Nat) (d : Int)
    (hn : 0<n) (_hm : 0<m) (hdiv : n%m=0) (hprev : 2^m+3 ∣ L)
    (hsmall : n/m<2^m+3)
    (hlegal : (L:Int)*((2:Int)^m+3) ∣ (2:Int)^n+d+(L:Int)*(5-2*(m:Int))) :
    d+(L:Int)*(5-2*(m:Int))≠ -(-3:Int)^(n/m) := by
  intro hc
  have hh := repeated_parameter_requires_quotient n L m d hn _hm hdiv hprev hc hlegal
  have he : m*(n/m)=n := by have hh:=Nat.div_add_mod n m; omega
  have hk : 0<n/m := by
    by_cases hz : n/m=0
    · rw [hz,Nat.mul_zero] at he; omega
    · exact Nat.pos_of_ne_zero hz
  have := Nat.le_of_dvd hk hh
  omega

/-- Congruence survives a natural power without a primality assumption. -/
theorem dvd_pow_difference (D x y : Int) (k : Nat) (h : D ∣ x-y) :
    D ∣ x^k-y^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨z,hz⟩ := ih
    obtain ⟨w,hw⟩ := h
    refine ⟨z*x+y^k*w,?_⟩
    rw [Int.pow_succ,Int.pow_succ]
    grind

/-- Every previous denominator imposes a cross-parameter order constraint
on the signed-power cancellation quotient. -/
theorem previous_denominator_order (n L m a : Nat) (d : Int)
    (_hdiv : n%m=0) (hprev : 2^a+3 ∣ L)
    (hcan : d+(L:Int)*(5-2*(m:Int))= -(-3:Int)^(n/m))
    (hlegal : (L:Int)*((2:Int)^m+3) ∣ (2:Int)^n+d+(L:Int)*(5-2*(m:Int))) :
    (2:Int)^a+3 ∣ (-3:Int)^n-(-3:Int)^((n/m)*a) := by
  let D : Int := (2:Int)^a+3
  have hprevI : D ∣ (L:Int) := by dsimp [D]; exact_mod_cast hprev
  have hd := Int.dvd_trans (Int.dvd_trans hprevI (Int.dvd_mul_right (L:Int) ((2:Int)^m+3))) hlegal
  have hnum : (2:Int)^n+d+(L:Int)*(5-2*(m:Int))=(2:Int)^n-(-3:Int)^(n/m) := by omega
  rw [hnum] at hd
  have h1 := dvd_pow_difference D ((2:Int)^n) ((-3:Int)^(n/m)) a hd
  have hd2 : D ∣ (2:Int)^a-(-3:Int) := by exact ⟨1,by dsimp [D]; omega⟩
  have h2 := dvd_pow_difference D ((2:Int)^a) (-3) n hd2
  rw [←Int.pow_mul,←Int.pow_mul] at h1
  rw [←Int.pow_mul] at h2
  rw [Nat.mul_comm n a] at h1
  have h3 := Int.dvd_sub h1 h2
  have he : (2:Int)^(a*n)-(-3:Int)^((n/m)*a)-((2:Int)^(a*n)-(-3:Int)^n)=(-3:Int)^n-(-3:Int)^((n/m)*a) := by omega
  rwa [he] at h3

#print axioms linearize
#print axioms denominator_coprime
#print axioms square_requires_quotient
#print axioms repeated_parameter_requires_quotient
#print axioms repeated_parameter_exclusion
#print axioms previous_denominator_order
end NeedleCancellationRepeat

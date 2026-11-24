import RotationSparse

namespace NeedleRotation

def geom (s : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => 1+2^s*geom s n

theorem geom_lt (s n : Nat) (hs : 0<s) : geom s n < 2^(n*s) := by
  have h2 : 2≤2^s := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 1≤s by omega)
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    simp only [geom,Nat.succ_mul,Nat.pow_add]
    have hh := Nat.mul_le_mul_left (2^s) (show geom s n+1≤2^(n*s) by omega)
    rw [Nat.mul_add,Nat.mul_one] at hh
    rw [Nat.mul_comm (2^(n*s))]
    omega

theorem geom_odd (s n : Nat) (hs : 0<s) (hn : 0<n) : (geom s n)%2=1 := by
  cases n with
  | zero => omega
  | succ n =>
    have hpow : (2:Nat)^s%2=0 := by
      rw [show s=s-1+1 by omega,Nat.pow_succ,Nat.mul_mod]
      simp
    change (1+2^s*geom s n)%2=1
    rw [Nat.add_mod, Nat.mul_mod, hpow]
    simp

/-- Scaling by 2^(n*s) when m=a+s turns every signed geometric term
into the same 3-power times a nonnegative geometric sum. -/
theorem near_congruence (a s n : Nat) (c : Int) :
    denominator (a+s) ∣ (2:Int)^(n*s)*value (sparse a c n)-c*(-3)^n*(geom s n : Int) := by
  induction n generalizing c with
  | zero => simp [sparse,geom,value]
  | succ n ih =>
    have hpow : denominator (a+s) ∣ ((2:Int)^(a+s))^(n+1)-(-3)^(n+1) :=
      dvd_power_difference _ _ _ (by
        have he : (2:Int)^(a+s)-(-3)=denominator (a+s) := by simp [denominator]
        rw [he]
        exact Int.dvd_refl _) _
    have htop : denominator (a+s) ∣ c*(2:Int)^((n+1)*s)*(2:Int)^((n+1)*a)-c*(-3)^(n+1) := by
      have he : (2:Int)^((n+1)*s)*(2:Int)^((n+1)*a)=((2:Int)^(a+s))^(n+1) := by
        rw [←Int.pow_add,←Int.pow_mul]
        congr 1
        simp only [Nat.add_mul,Nat.mul_add]
        grind
      rw [Int.mul_assoc,he,←Int.mul_sub]
      exact Int.dvd_mul_of_dvd_right hpow
    have hrest := ih (-3*c)
    have hscaled : denominator (a+s) ∣ (2:Int)^s*((2:Int)^(n*s)*value (sparse a (-3*c) n)-(-3*c)*(-3)^n*(geom s n : Int)) := Int.dvd_mul_of_dvd_right hrest
    have he : (2:Int)^((n+1)*s)*value (sparse a c (n+1))-c*(-3)^(n+1)*(geom s (n+1) : Int) =
       (c*(2:Int)^((n+1)*s)*(2:Int)^((n+1)*a)-c*(-3)^(n+1))+
       (2:Int)^s*((2:Int)^(n*s)*value (sparse a (-3*c) n)-(-3*c)*(-3)^n*(geom s n : Int)) := by
      simp only [sparse,value,geom,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Nat.succ_mul,Int.pow_add,Int.pow_succ]
      grind
    rw [he]
    exact Int.dvd_add htop hscaled

/-- Exact exclusion of the high-side near strip, with explicit mass bound. -/
theorem near_no_dvd (a s n B v : Nat) (u C : Int)
    (hs : 0<s) (hn : 0<n) (hv : v<n*s) (hu : u%2=1)
    (hbound : (u*2^v).natAbs*3^n+C.natAbs<2^B)
    (hsize : B+n*s≤a+s) :
    ¬ denominator (a+s) ∣ value ((C,0)::sparse a (u*2^v) n) := by
  intro hd
  let c := u*2^v
  let R := c*(-3)^n*(geom s n : Int)+C*2^(n*s)
  have h1 : denominator (a+s) ∣ (2:Int)^(n*s)*value ((C,0)::sparse a c n) := Int.dvd_mul_of_dvd_right hd
  have h2 := near_congruence a s n c
  have hdiff : (2:Int)^(n*s)*value ((C,0)::sparse a c n) - R =
       (2:Int)^(n*s)*value (sparse a c n)-c*(-3)^n*(geom s n : Int) := by
    simp only [value,Int.pow_zero,Int.mul_one,R]
    grind
  have hR : denominator (a+s) ∣ R := by
    have hsub := Int.dvd_sub h1 (show denominator (a+s) ∣ (2:Int)^(n*s)*value ((C,0)::sparse a c n)-R by rw [hdiff]; exact h2)
    have he : (2:Int)^(n*s)*value ((C,0)::sparse a c n)-((2:Int)^(n*s)*value ((C,0)::sparse a c n)-R)=R := by omega
    rwa [he] at hsub
  have hg := geom_lt s n hs
  have hmass : R.natAbs < 2^(B+n*s) := by
    have htri := Int.natAbs_add_le (c*(-3)^n*(geom s n : Int)) (C*2^(n*s))
    change R.natAbs≤_ at htri
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at htri
    have hbound' : c.natAbs*3^n+C.natAbs<2^B := hbound
    calc
      R.natAbs ≤ c.natAbs*3^n*geom s n+C.natAbs*2^(n*s) := htri
      _ ≤ (c.natAbs*3^n+C.natAbs)*2^(n*s) := by
        simp only [Nat.add_mul,Nat.mul_add]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_of_lt hg)) _
      _ < 2^(B+n*s) := by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hbound' (Nat.two_pow_pos _)
  have hzero : R=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hR (by
    have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hsize
    have heq : (denominator (a+s)).natAbs=2^(a+s)+3 := by simp [denominator,Int.natAbs_pow,Int.natAbs_add_of_nonneg,Int.pow_nonneg]
    rw [heq]
    omega)
  have hgo : (geom s n : Int)%2=1 := by exact_mod_cast geom_odd s n hs hn
  have huo : (u*(-3)^n*(geom s n : Int))%2=1 := by rw [Int.mul_emod,odd_mul_neg_three_pow u n hu,hgo]; decide
  have hnon := three_odd_min (u*(-3)^n*(geom s n : Int)) C 0 v (n*s) (n*s+1) huo hv (by omega)
  apply hnon
  simp only [R,c] at hzero
  simp only [Int.zero_mul,Int.add_zero]
  grind

#print axioms near_congruence
#print axioms near_no_dvd
end NeedleRotation

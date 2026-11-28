import DyadicSignedGap
import DyadicReach

namespace BB6.Agent21Dyadic

theorem signed_singleton_numer (x y : Int) (r : Nat)
    (hr : (r:Int)%2=(y+1)%2) :
    signedZ x y+acc (signedS x y) [r] =
      -(x+y+(x+y)%2) := by
  simp only [acc,Int.mul_zero,Int.add_zero]
  rw [signed_one_numer,signed_parity_cost x y r hr]
  omega

/-- The all-precision base case of the prospective dyadic-word /
    modular-cone duality: if the adjusted sum has b factors of 2,
    there is an explicit compatible singleton completed or pending
    word. No inverse search is needed. -/
theorem signed_open_if_divisible (x y : Int) (n : Nat)
    (hn : 0<n) (hq : P n∣x+y+(x+y)%2) :
    OpenAt (signedS x y) (signedZ x y) n := by
  have hneg : P n∣-(x+y+(x+y)%2) := by
    obtain ⟨k,hk⟩ := hq
    refine ⟨-k,?_⟩
    rw [hk,Int.mul_neg]
  by_cases hpar : (n:Int)%2=(y+1)%2
  · left
    refine ⟨[n],by simp [Positive,hn],by simp [cost],?_⟩
    rw [signed_singleton_numer x y n hpar]
    exact hneg
  · right
    refine ⟨[],n+1,by omega,by simp [Positive],by simp [cost],?_⟩
    simp only [List.nil_append]
    have hnext : ((n+1:Nat):Int)%2=(y+1)%2 := by
      push_cast
      omega
    rw [signed_singleton_numer x y (n+1) hnext]
    exact hneg

theorem signed_open_zero (x y : Int) :
    OpenAt (signedS x y) (signedZ x y) 0 := open_zero _ _

theorem signed_open_one (x y : Int) :
    OpenAt (signedS x y) (signedZ x y) 1 := by
  apply signed_open_if_divisible x y 1 (by decide)
  change (2:Int)∣x+y+(x+y)%2
  exact Int.dvd_of_emod_eq_zero (by omega)

#print axioms signed_open_if_divisible
#print axioms signed_open_one
end BB6.Agent21Dyadic

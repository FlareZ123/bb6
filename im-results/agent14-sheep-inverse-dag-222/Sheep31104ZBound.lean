import Std
set_option exponentiation.threshold 100000
namespace Sheep31104ZBound

private theorem pow_mod_period (m p r k : Nat) (hm : 1<m)
    (hp : 2^p % m=1) : 2^(r+p*k)%m=2^r%m := by
  rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m,hp]
  simp [Nat.mod_eq_of_lt hm]

/-- Every candidate even parent of Z has hidden odd-run exponent zero. -/
theorem Z_hidden_h_zero (k y h u : Nat)
    (ht : 3483*y+16576=2^(31114+40824*k))
    (hy : y=1+3^h*u) : h=0 := by
  have hp : 2^1134%10449=1 := by decide
  have he : 31114+40824*k=31114+1134*(36*k) := by omega
  have hc : 2^(31114+40824*k)%10449=6127 := by
    rw [he,pow_mod_period 10449 1134 31114 (36*k) (by decide) hp]
  by_cases hzero : h=0
  · exact hzero
  have hge : 1≤h := by omega
  obtain ⟨t,rfl⟩ : ∃t,h=1+t := ⟨h-1,by omega⟩
  have hp3 : 3^(1+t)=3*3^t := by rw [Nat.pow_add]
  have hrep : y=1+3*(3^t*u) := by rw [hy,hp3]; simp [Nat.mul_assoc]
  rw [hrep] at ht
  have hprod (z : Nat) : 3483*(1+3*z)+16576=20059+10449*z := by omega
  have hcalc : 2^(31114+40824*k)=20059+10449*(3^t*u) := by
    rw [←ht]
    exact hprod (3^t*u)
  have hm : 2^(31114+40824*k)%10449=9610 := by
    rw [hcalc]
    simp [Nat.add_mod]
  omega

#print axioms Z_hidden_h_zero
end Sheep31104ZBound

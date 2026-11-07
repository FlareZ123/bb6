import Std
set_option exponentiation.threshold 100000
namespace Sheep31104TBound
private theorem pow_mod_period (m p r k : Nat) (hm : 1<m)
    (hp : 2^p %m=1) : 2^(r+p*k)%m=2^r%m := by
  rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m,hp]
  simp [Nat.mod_eq_of_lt hm]

/-- Every possible even E edge into the terminal T has hidden h=0. -/
theorem T_hidden_h_zero (k y h u : Nat)
    (ht : 31347*y+174404=2^(31117+40824*k))
    (hy : y=1+3^h*u) : h=0 := by
  have hp : 2^10206%94041=1 := by decide
  have he : 31117+40824*k=31117+10206*(4*k) := by omega
  have hc : 2^(31117+40824*k)%94041=49016 := by
    rw [he,pow_mod_period 94041 10206 31117 (4*k) (by decide) hp]
  by_cases hzero : h=0
  · exact hzero
  have hge : 1≤h := by omega
  obtain ⟨t,rfl⟩ : ∃t,h=1+t := ⟨h-1,by omega⟩
  have hp3 : 3^(1+t)=3*3^t := by rw [Nat.pow_add]
  have hrep : y=1+3*(3^t*u) := by rw [hy,hp3]; simp [Nat.mul_assoc]
  rw [hrep] at ht
  have hprod (z:Nat) : 31347*(1+3*z)+174404=205751+94041*z := by omega
  have hcalc : 2^(31117+40824*k)=205751+94041*(3^t*u) := by
    rw [←ht]
    exact hprod (3^t*u)
  have hm : 2^(31117+40824*k)%94041=17669 := by
    rw [hcalc]
    simp [Nat.add_mod]
  omega

#print axioms T_hidden_h_zero
end Sheep31104TBound

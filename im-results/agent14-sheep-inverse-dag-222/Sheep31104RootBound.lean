import Std
set_option exponentiation.threshold 100000
namespace Sheep31104RootBound

private theorem pow_mod_period (m p r k : Nat) (hm:1<m)
    (hp:2^p%m=1):2^(r+p*k)%m=2^r%m := by
  rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m,hp]
  simp [Nat.mod_eq_of_lt hm]

/-- Uniform 3-adic bound: every root inverse has hidden h<7. -/
theorem root_h_lt_seven (k h u:Nat)
    (hy : 2^(31104+122472*k)=1+3^h*u) : h<7 := by
  have hp:2^1458%2187=1 := by decide
  have he:31104+122472*k=31104+1458*(84*k) := by omega
  have hmod:2^(31104+122472*k)%2187=730 := by
    rw [he,pow_mod_period 2187 1458 31104 (84*k) (by decide) hp]
  by_cases hh:h<7
  · exact hh
  have hge:7≤h := by omega
  obtain ⟨t,rfl⟩ : ∃t,h=7+t := ⟨h-7,by omega⟩
  have hpow:3^(7+t)=2187*3^t := by rw [Nat.pow_add]
  rw [hpow] at hy
  have hm:2^(31104+122472*k)%2187=1 := by
    rw [hy,Nat.add_mod]
    have hz:(2187*3^t*u)%2187=0 := by simp [Nat.mul_mod]
    rw [hz]
  omega
#print axioms root_h_lt_seven
end Sheep31104RootBound

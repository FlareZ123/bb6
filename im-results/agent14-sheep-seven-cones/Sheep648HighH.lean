import Std
import Sheep648Period
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000

namespace Sheep648HighH

/-- Uniform 3-adic root nondivisibility, for j=648+122472k. -/
theorem root_not_one_mod729 (k : Nat) :
    2^(648+122472*k) % 729 ≠ 1 := by
  have hp : 2^486 % 729 = 1 := by decide
  have he : 648+122472*k = 162+486*(1+252*k) := by omega
  rw [he, Sheep648Period.pow_mod_period 729 486 162 (1+252*k) (by decide) hp]
  decide

/-- Uniform 3-adic child congruence. -/
theorem child_not_3415_mod6561 (k : Nat) :
    2^(656+122472*k) % 6561 ≠ 3415 := by
  have hp : 2^4374 % 6561 = 1 := by decide
  have he : 656+122472*k = 656+4374*(28*k) := by omega
  rw [he, Sheep648Period.pow_mod_period 6561 4374 656 (28*k) (by decide) hp]
  decide

/-- Every source edge into the root has hidden odd-block length below six. -/
theorem root_h_lt_six (k h u : Nat)
    (hy : 2^(648+122472*k) = 1+3^h*u) : h < 6 := by
  by_cases hh : h < 6
  · exact hh
  have hge : 6 ≤ h := by omega
  obtain ⟨t, rfl⟩ : ∃ t, h=6+t := ⟨h-6,by omega⟩
  have hp : 3^(6+t) = 729*3^t := by rw [Nat.pow_add]
  rw [hp] at hy
  have hm : 2^(648+122472*k) % 729 = 1 := by
    rw [hy, Nat.add_mod]
    have hz : (729*3^t*u)%729=0 := by simp [Nat.mul_mod]
    rw [hz]
  exact False.elim (root_not_one_mod729 k hm)

/-- Any candidate E predecessor of child (2187*y+1228=2^(656+Pk))
must have h=0, for all k. -/
theorem child_h_zero (k y h u : Nat)
    (ht : 2187*y+1228=2^(656+122472*k))
    (hy : y = 1+3^h*u) : h=0 := by
  by_cases hh : h=0
  · exact hh
  have hge : 1 ≤ h := by omega
  obtain ⟨t,rfl⟩ : ∃ t, h=1+t := ⟨h-1,by omega⟩
  have hp : 3^(1+t)=3*3^t := by rw [Nat.pow_add]
  have hrep : y=1+3*(3^t*u) := by rw [hy,hp]; simp [Nat.mul_assoc]
  rw [hrep] at ht
  have hprod (z : Nat) : 2187*(1+3*z)+1228=3415+6561*z := by omega
  have hcalc : 2^(656+122472*k)=3415+6561*(3^t*u) := by
    rw [←ht]
    exact hprod (3^t*u)
  have hm : 2^(656+122472*k)%6561=3415 := by
    rw [hcalc]
    simp [Nat.add_mod]
  exact False.elim (child_not_3415_mod6561 k hm)

#print axioms root_h_lt_six
#print axioms child_h_zero
end Sheep648HighH

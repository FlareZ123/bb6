import Std
namespace BB6.Agent45Quarter

theorem pow_at_least_linear (q : Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.pow_succ]
    omega

/-- Without huge numeral evaluation: 2^(r-18) beats 32*(r+1) for all r≥34. -/
theorem exp_dominates_residue (r : Nat) (hr : 34≤r) :
    32*(r+1)≤2^(r-18) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases h : r=34
    · subst r
      decide
    · have hp := ih (r-1) (by omega) (by omega : 34≤r-1)
      have he : r-18=(r-1-18)+1 := by omega
      rw [he,Nat.pow_succ]
      omega

/-- Uniform affine parameter lower bound valid at every quarter residue r≥34. -/
theorem quarter_exponent_bound (r q : Nat) (hr : 34≤r) :
    32*(q+r+1)≤2^(262144*q+(r-18)) := by
  have hq := pow_at_least_linear q
  have hqe : q+1 ≤ 2^(262144*q) := by
    have hpow : 2^q ≤ 2^(262144*q) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hbase := exp_dominates_residue r hr
  have hlin : q+r+1 ≤ (r+1)*(q+1) := by
    calc
      q+r+1 ≤ r*q+q+r+1 := by omega
      _ = (r+1)*(q+1) := by simp [Nat.mul_add, Nat.add_mul]; omega
  rw [Nat.pow_add]
  calc
    32*(q+r+1) ≤ (32*(r+1))*(q+1) := by
      calc
        32*(q+r+1) ≤ 32*((r+1)*(q+1)) := Nat.mul_le_mul_left 32 hlin
        _ = (32*(r+1))*(q+1) := by rw [Nat.mul_assoc]
    _ ≤ 2^(r-18)*2^(262144*q) := Nat.mul_le_mul hbase hqe
    _ = 2^(262144*q)*2^(r-18) := by ac_rfl
#print axioms BB6.Agent45Quarter.quarter_exponent_bound
end BB6.Agent45Quarter

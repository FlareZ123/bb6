import Std
set_option maxHeartbeats 0
namespace CascadeAgent44

theorem two_three_log_step (r : Nat) (hr : 0 < r) :
    Nat.log2 (2*r) ≤ Nat.log2 (3*r) ∧
    Nat.log2 (3*r) ≤ Nat.log2 (2*r)+1 := by
  let j := Nat.log2 (2*r)
  have hP : 2^j ≤ 2*r := Nat.log2_self_le (by omega)
  have hU : 2*r < 2^(j+1) := Nat.lt_log2_self
  have hL : j ≤ Nat.log2 (3*r) := by
    apply (Nat.le_log2 (by omega)).mpr
    omega
  have hPow : 2^(j+2)=2*2^(j+1) := by
    rw [show j+2=(j+1)+1 by omega,Nat.pow_succ]
    omega
  have hu : 3*r < 2^(j+2) := by
    rw [hPow]
    omega
  have hL' : Nat.log2 (3*r) < j+2 :=
    (Nat.log2_lt (by omega)).mpr hu
  exact ⟨hL, by omega⟩

#print axioms two_three_log_step
end CascadeAgent44

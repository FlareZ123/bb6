import Lean
import BRunValuation

namespace BB6.CryptidBRun

theorem run_end_quadratic {j n z : Nat} (h : BRun j n z) :
    5*z+11 ≤ (5*n+11)*(5*n+11) := by
  let N := 5*n+11
  let P := 3^j
  have hN : 0 < N := by dsimp [N]; omega
  have hP : P ≤ N := Nat.le_of_dvd hN (run_requires_three_power h)
  have h8 : 8^j ≤ P*P := by
    calc
      8^j ≤ 9^j := Nat.pow_le_pow_left (by decide) j
      _ = (3*3)^j := by rfl
      _ = P*P := by simpa [P] using Nat.mul_pow 3 3 j
  have hb : P*(5*z+11) ≤ P*(N*N) := by
    calc
      P*(5*z+11) = (8^j)*N := run_scale h
      _ ≤ (P*P)*N := Nat.mul_le_mul_right N h8
      _ ≤ (P*N)*N := Nat.mul_le_mul_right N (Nat.mul_le_mul_left P hP)
      _ = P*(N*N) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hb (Nat.pow_pos (by decide))

theorem run_end_length_bound {j n z : Nat} (h : BRun j n z) :
    z ≤ (5*n+11)*(5*n+11) := by
  have hh := run_end_quadratic h
  omega

#print axioms run_end_quadratic
#print axioms run_end_length_bound
end BB6.CryptidBRun

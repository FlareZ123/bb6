import Std

namespace BB6.Agent9R2002
set_option maxHeartbeats 0

theorem generic_band (q X t A C : Nat)
    (ht : t + (q+1) = 7*X)
    (hX : 64*(q+1) ≤ X)
    (hAlo : 65960 ≤ A) (hAhi : A ≤ 130648)
    (hClo : 63930 ≤ C) (hChi : C ≤ 126628) :
    458752*X < A*t+C ∧ A*t+C < 917504*X := by
  have hl : 65960*t ≤ A*t := Nat.mul_le_mul_right t hAlo
  have hu : A*t ≤ 130648*t := Nat.mul_le_mul_right t hAhi
  omega

theorem no_fourteen_between (n v : Nat)
    (hl : 14*2^n < v) (hu : v < 14*2^(n+1)) :
    ∀ j : Nat, v ≠ 14*2^j := by
  intro j h
  by_cases hj : j≤n
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) hj
    have hm : 14*2^j ≤ 14*2^n := Nat.mul_le_mul_left 14 hp
    omega
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show n+1≤j by omega)
    have hm : 14*2^(n+1) ≤ 14*2^j := Nat.mul_le_mul_left 14 hp
    omega

#print axioms generic_band
#print axioms no_fourteen_between
end BB6.Agent9R2002

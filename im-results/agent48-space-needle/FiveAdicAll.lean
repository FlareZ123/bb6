import FiveAdicOrder
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic

/-- Exact first nonzero 5-adic digit for every multiple of 4*5^t. -/
theorem four_five_multiple_digit (t m : Nat) :
    ∃ h, 2^(4*5^t*m) = 1 + 3*m*5^(t+1)+h*5^(t+2) := by
  obtain ⟨h₀,h₀eq⟩ := five_adic_power_digit t
  let u := 3+5*h₀
  have hp : 5^(t+2)=5*5^(t+1) := by
    rw [show t+2=t+1+1 by omega, Nat.pow_succ']
  have hu : 2^(4*5^t)=1+5^(t+1)*u := by
    dsimp [u]
    rw [h₀eq,hp]
    have hx : 5^(t+1)*(3+5*h₀)=3*5^(t+1)+h₀*(5*5^(t+1)) := by
      rw [Nat.mul_add]
      ac_rfl
    omega
  obtain ⟨h₁,hh₁⟩ := five_digit_pow t u m
  refine ⟨m*h₀+h₁,?_⟩
  calc
    2^(4*5^t*m) = (2^(4*5^t))^m := by rw [Nat.pow_mul]
    _ = (1+5^(t+1)*u)^m := by rw [hu]
    _ = 1+(m*u)*5^(t+1)+h₁*5^(t+2) := hh₁
    _ = 1+3*m*5^(t+1)+(m*h₀+h₁)*5^(t+2) := by
      dsimp [u]
      rw [hp]
      simp only [Nat.mul_add,Nat.add_mul]
      simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      ac_rfl

/-- After exponent 4*5^t, the next 5-adic power divides precisely when
the remaining exponent multiplier is itself divisible by five. -/
theorem five_power_divides_iff (t m : Nat) :
    5^(t+2) ∣ 2^(4*5^t*m)-1 ↔ 5 ∣ m := by
  obtain ⟨h,hh⟩ := four_five_multiple_digit t m
  have hp : 5^(t+2)=5*5^(t+1) := by
    rw [show t+2=t+1+1 by omega, Nat.pow_succ']
  have hsub : 2^(4*5^t*m)-1 = 5^(t+1)*(3*m+5*h) := by
    rw [hh,hp]
    have he : 3*m*5^(t+1)+h*(5*5^(t+1)) = 5^(t+1)*(3*m+5*h) := by
      rw [Nat.mul_add]
      ac_rfl
    omega
  constructor
  · rintro ⟨z,hz⟩
    rw [hsub,hp] at hz
    have he : 5^(t+1)*(3*m+5*h) = 5^(t+1)*(5*z) := by
      rw [hz]
      ac_rfl
    have hpos : 0<5^(t+1) := Nat.pow_pos (by decide)
    have hc : 3*m+5*h=5*z := Nat.eq_of_mul_eq_mul_left hpos he
    have hm : m%5=0 := by omega
    exact Nat.dvd_of_mod_eq_zero hm
  · rintro ⟨z,rfl⟩
    rw [hsub,hp]
    refine ⟨3*z+h,?_⟩
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl

#print axioms four_five_multiple_digit
#print axioms five_power_divides_iff
end BB6.Agent48.FiveAdic

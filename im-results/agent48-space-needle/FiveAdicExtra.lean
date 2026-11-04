import FiveAdicLift
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic

theorem five_power_divides (t : Nat) : 5^(t+1) ∣ 2^(4*5^t)-1 := by
  obtain ⟨h,hh⟩ := five_adic_power_digit t
  have hp : 5^(t+2)=5*5^(t+1) := by rw [show t+2=t+1+1 by omega,Nat.pow_succ']
  have hh' : 2^(4*5^t)-1 = 5^(t+1) * (3+5*h) := by
    rw [hh,hp]
    rw [Nat.mul_add]
    have hx : 3*5^(t+1)+h*(5*5^(t+1)) = 5^(t+1)*3+5^(t+1)*(5*h) := by ac_rfl
    omega
  exact ⟨3+5*h,hh'⟩

theorem five_power_not_extra (t : Nat) : ¬ 5^(t+2) ∣ 2^(4*5^t)-1 := by
  obtain ⟨h,hh⟩ := five_adic_power_digit t
  have hp : 5^(t+2)=5*5^(t+1) := by rw [show t+2=t+1+1 by omega,Nat.pow_succ']
  have hh' : 2^(4*5^t)-1 = 5^(t+1)*(3+5*h) := by
    rw [hh,hp]
    have hx : 3*5^(t+1)+h*(5*5^(t+1)) = 5^(t+1)*(3+5*h) := by
      rw [Nat.mul_add]
      ac_rfl
    omega
  rintro ⟨u,hu⟩
  rw [hh',hp] at hu
  have he : 5^(t+1)*(3+5*h) = 5^(t+1)*(5*u) := by
    rw [hu]
    ac_rfl
  have hpos : 0 < 5^(t+1) := Nat.pow_pos (by omega)
  have hc := Nat.eq_of_mul_eq_mul_left hpos he
  omega

#print axioms five_power_divides
#print axioms five_power_not_extra
end BB6.Agent48.FiveAdic

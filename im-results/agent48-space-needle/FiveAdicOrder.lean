import FiveAdicExtra
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic

private theorem linear_digit_mul (B u m h : Nat) :
  (1+m*u*(5*B)+h*(25*B))*(1+u*(5*B)) =
  1+(m+1)*u*(5*B)+(h+m*u*u*B+h*u*(5*B))*(25*B) := by
  simp only [Nat.mul_add,Nat.add_mul]
  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  ac_rfl

/-- First 5-adic digit under an arbitrary natural exponent. -/
theorem five_digit_pow (t u m : Nat) :
    ∃ h, (1+5^(t+1)*u)^m=1+(m*u)*5^(t+1)+h*5^(t+2) := by
  induction m with
  | zero =>
      refine ⟨0,?_⟩
      simp
  | succ m ih =>
      obtain ⟨h,hh⟩ := ih
      refine ⟨h+m*u*u*5^t+h*u*5^(t+1),?_⟩
      have hp1 : 5^(t+1)=5*5^t := by rw [Nat.pow_succ']
      have hp2 : 5^(t+2)=25*5^t := by
        rw [show t+2=t+1+1 by omega,Nat.pow_succ',hp1]
        rw [show (25:Nat)=5*5 by decide]
        ac_rfl
      calc
        (1+5^(t+1)*u)^(m+1) = (1+5^(t+1)*u)^m*(1+5^(t+1)*u) := by
          rw [Nat.pow_succ']
          ac_rfl
        _ = (1+(m*u)*5^(t+1)+h*5^(t+2))*(1+5^(t+1)*u) := by rw [hh]
        _ = 1+((m+1)*u)*5^(t+1)+(h+m*u*u*5^t+h*u*5^(t+1))*5^(t+2) := by
          rw [hp1,hp2]
          simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using linear_digit_mul (5^t) u m h

#print axioms five_digit_pow
end BB6.Agent48.FiveAdic

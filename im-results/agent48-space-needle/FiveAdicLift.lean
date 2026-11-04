import Lean
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic

def P (w : Nat) := 2+10*w+25*w^2+25*w^3

theorem binomial_five (w : Nat) :
    (1+5*w)^5 = 1 + 25*w + 125*w^2*P w := by
  dsimp [P]
  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2 : w*(w*250) = 10*(w*(w*25)) := by
    rw [show (250:Nat)=10*25 by decide]
    ac_rfl
  have h3 : w*(w*(w*1250)) = 10*(w*(w*(w*125))) := by
    rw [show (1250:Nat)=10*125 by decide]
    ac_rfl
  have h4 : w*(w*(w*(w*3125))) = 5*(w*(w*(w*(w*625)))) := by
    rw [show (3125:Nat)=5*625 by decide]
    ac_rfl
  omega

theorem lift_pow_five (t u : Nat) :
    (1+5^(t+1)*u)^5 =
      1+5^(t+2)*u + 5^(t+3)*(5^t*u^2*P (5^t*u)) := by
  have hpow1 : 5^(t+1)=5*5^t := by
    rw [Nat.pow_succ']
  have hpow2 : 5^(t+2)=25*5^t := by
    rw [show t+2=t+1+1 by omega,Nat.pow_succ',hpow1]
    rw [show (25:Nat)=5*5 by decide]
    ac_rfl
  have hpow3 : 5^(t+3)=125*5^t := by
    rw [show t+3=t+2+1 by omega,Nat.pow_succ',hpow2]
    rw [show (125:Nat)=5*25 by decide]
    ac_rfl
  calc
    (1+5^(t+1)*u)^5 = (1+5*(5^t*u))^5 := by
      rw [hpow1]
      ac_rfl
    _ = 1+25*(5^t*u)+125*(5^t*u)^2*P (5^t*u) := binomial_five _
    _ = 1+5^(t+2)*u+5^(t+3)*(5^t*u^2*P (5^t*u)) := by
      rw [hpow2,hpow3]
      have hsq1 : (5^t*u)^2=(5^t*u)*(5^t*u) := by simp [Nat.pow_succ']
      have hsq2 : u^2=u*u := by simp [Nat.pow_succ']
      rw [hsq1,hsq2]
      ac_rfl

/-- Exact first nonzero 5-adic digit of 2^(4*5^t)-1. -/
theorem five_adic_power_digit (t : Nat) :
    ∃ h, 2^(4*5^t) = 1+3*5^(t+1)+h*5^(t+2) := by
  induction t with
  | zero =>
      refine ⟨0, ?_⟩
      decide
  | succ t ih =>
      obtain ⟨h,hh⟩ := ih
      let u := 3+5*h
      have hp : 5^(t+2) = 5*5^(t+1) := by
        rw [show t+2=t+1+1 by omega, Nat.pow_succ']
      have hu : 2^(4*5^t) = 1+5^(t+1)*u := by
        rw [hh]
        dsimp [u]
        rw [hp]
        simp only [Nat.mul_add]
        have he : 5^(t+1)*(5*h)=h*(5*5^(t+1)) := by ac_rfl
        omega
      have hm : 5^(t+2)*u = 3*5^(t+2)+h*5^(t+3) := by
        dsimp [u]
        have hp3 : 5^(t+3)=5*5^(t+2) := by
          rw [show t+3=t+2+1 by omega, Nat.pow_succ']
        rw [hp3]
        simp only [Nat.mul_add]
        have he : 5^(t+2)*(5*h)=h*(5*5^(t+2)) := by ac_rfl
        omega
      refine ⟨h+5^t*u^2*P (5^t*u), ?_⟩
      calc
        2^(4*5^(t+1)) = (2^(4*5^t))^5 := by
          have hexp : 4*5^(t+1)=(4*5^t)*5 := by
            rw [Nat.pow_succ']
            ac_rfl
          rw [hexp,Nat.pow_mul]
        _ = (1+5^(t+1)*u)^5 := by rw [hu]
        _ = 1+5^(t+2)*u+5^(t+3)*(5^t*u^2*P (5^t*u)) := lift_pow_five t u
        _ = 1+3*5^(t+2)+(h+5^t*u^2*P (5^t*u))*5^(t+3) := by
          rw [hm, Nat.add_mul]
          ac_rfl

#print axioms five_adic_power_digit
end BB6.Agent48.FiveAdic
#print axioms BB6.Agent48.FiveAdic.binomial_five
#print axioms BB6.Agent48.FiveAdic.lift_pow_five

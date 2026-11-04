import FirstReturnCore
import SweepInvariant

namespace CascadeResetInverse
open CascadeSource CascadeSweep

private theorem reach_trans {x y z : Nat × Nat} (hxy : ReachC x y) (hyz : ReachC y z) :
    ReachC x z := by
  induction hyz with
  | refl => exact hxy
  | push hstep he ih => exact ReachC.push ih he

/-- Every dyadic q=2^t*d with odd d and q≥4 follows the entire finite B=2
    drain to the next reset, with no intermediate reset or halt. -/
theorem drain_power (t d : Nat) (hd : d%2=1) (hq : 4≤2^t*d) :
    ReachC (2^t*d-3,2) ((3^(t+1)*d-5)/2,0) := by
  induction t generalizing d with
  | zero =>
    have hd4 : 4 ≤ d := by simpa using hq
    have hd5 : 5 ≤ d := by omega
    have hnext := drain_odd d hd5 hd
    simpa using (ReachC.push (ReachC.refl (d-3,2)) hnext)
  | succ t ih =>
    have heven : (2^(t+1)*d)%2=0 := by
      have hp : 2^(t+1)*d=2*(2^t*d) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      rw [hp]
      omega
    have hnext := drain_even (2^(t+1)*d) hq heven
    have hstep : Cstep (2^(t+1)*d-3) 2 =
        some (2^t*(3*d)-3,2) := by
      have hpow : 2^(t+1)*d=2*(2^t*d) := by rw [Nat.pow_succ]; simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      have hx : 2^t*(3*d)=3*(2^t*d) := by
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      have hdiv : 3*(2^(t+1)*d)/2 = 2^t*(3*d) := by
        rw [hpow, hx]
        omega
      simpa only [hdiv] using hnext
    have hd3 : (3*d)%2=1 := by omega
    have hq3 : 4≤2^t*(3*d) := by
      have hpow : 2^(t+1)*d=2*(2^t*d) := by rw [Nat.pow_succ]; simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      have hx : 2^t*(3*d)=3*(2^t*d) := by simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      rw [hpow] at hq
      rw [hx]
      omega
    have hrec := ih (3*d) hd3 hq3
    have hprod : 3^(t+1)*(3*d) = 3^((t+1)+1)*d := by
      simp only [Nat.pow_succ,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
    rw [hprod] at hrec
    exact reach_trans (ReachC.push (ReachC.refl _) hstep) hrec

#print axioms drain_power
end CascadeResetInverse

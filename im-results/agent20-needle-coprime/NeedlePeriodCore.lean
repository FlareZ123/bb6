import Lean.Elab.Tactic.Omega
namespace NeedlePeriodCore

theorem periodic_mod (d K T b : Nat)
    (hbase : (2:Nat)^K % d = b % d)
    (hperiod : (2:Nat)^T % d = 1)
    (t : Nat) : (2:Nat)^(K+T*t)%d = b%d := by
  induction t with
  | zero => simpa using hbase
  | succ t ih =>
      have hexp : K+T*(t+1) = (K+T*t)+T := by
        simp [Nat.mul_add, Nat.add_left_comm, Nat.add_comm]
      rw [hexp, Nat.pow_add, Nat.mul_mod]
      rw [ih, hperiod]
      simp

#print axioms periodic_mod
end NeedlePeriodCore

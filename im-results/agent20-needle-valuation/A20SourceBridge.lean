import SpaceNeedleClosed
import A20NeedleGap
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- On the authentic Space Needle high-level map, an immediate predecessor
    of terminal level k has two-adic valuation at most k/2. -/
theorem terminal_incoming_valuation_bound (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    2*v ≤ k := by
  have heq := (predecessor_power_identity q v k).mp h
  have hkpow : 2^(k+2) = 2 * 2^(k+1) := by
    rw [show k+2=(k+1)+1 by omega, Nat.pow_succ]
    omega
  have hvpow : 2^(v+1) = 2 * 2^v := by rw [Nat.pow_succ]; omega
  rw [hkpow, hvpow] at heq
  have hsplit : (2*2^v+3)*(2*q+3)+2*v =
    2*(2^v*(2*q+3)+v+3*(q+1))+3 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hsplit] at heq
  have hcore : 2^v*(2*q+3)+v+3*(q+1)=2^(k+1) := by omega
  have hbound := NeedleGap.gap_all q v (k+1) hcore
  omega

#print axioms terminal_incoming_valuation_bound
end BB6.Agent20.SpaceNeedle

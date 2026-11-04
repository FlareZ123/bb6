import SpaceNeedleClosed
import A20NeedleGap
import A20UniqueBoundary
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

private theorem terminal_equation (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    2^v*(2*q+3)+v+3*(q+1)=2^(k+1) := by
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
  omega

/-- Every actual high-level immediate predecessor of a terminal tower
    at index k has two-adic valuation at most k/2. -/
theorem terminal_incoming_valuation_bound (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    2*v ≤ k := by
  have hcore := terminal_equation q v k h
  have hbound := NeedleGap.gap_all q v (k+1) hcore
  omega

/-- Equality in the valuation bound is the single explicit original-source
    predecessor: v=6, q=61, terminal tower index k=12. -/
theorem terminal_boundary_unique (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)))
    (he : k=2*v) : v=6 ∧ q=61 ∧ k=12 := by
  have hcore := terminal_equation q v k h
  have hb : k+1=2*v+1 := by omega
  obtain ⟨hv,hq⟩ := NeedleGap.gap_equality_unique q v (k+1) hcore hb
  refine ⟨hv,hq,?_⟩
  omega

/-- Except for that one predecessor, the valuation inequality is strict. -/
theorem terminal_incoming_strict (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)))
    (hne : v ≠ 6 ∨ q ≠ 61) : 2*v < k := by
  have hcore := terminal_equation q v k h
  have hbound := NeedleGap.gap_strict_except_unique q v (k+1) hcore hne
  omega

#print axioms terminal_incoming_valuation_bound
#print axioms terminal_boundary_unique
#print axioms terminal_incoming_strict
end BB6.Agent20.SpaceNeedle

import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleTriple
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

theorem distinct_three_oddTowers (q0 q3 q20 : Nat) :
    oddTower q0 0 ≠ oddTower q3 3 ∧
    oddTower q0 0 ≠ oddTower q20 20 ∧
    oddTower q3 3 ≠ oddTower q20 20 := by
  have h0 := oddTower_factor q0 0
  have h3 := oddTower_factor q3 3
  have h20 := oddTower_factor q20 20
  have p0 : (2:Nat)^0=1 := by decide
  have p3 : (2:Nat)^3=8 := by decide
  have p20 : (2:Nat)^20=1048576 := by decide
  rw [p0] at h0
  rw [p3] at h3
  rw [p20] at h20
  omega

#print axioms distinct_three_oddTowers
end BB6.Agent20.SpaceNeedleTriple

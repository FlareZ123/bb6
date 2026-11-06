import NeedleVariableValuation
import NeedleTerminalAffineSource
import Lean.Elab.Tactic.Omega

/-!
An all-parameter source-certified family of *synthetic* incoming Space Needle
terminal edges, with 2-adic source valuation unbounded. This does not assert
that any source is visited from the blank tape N 1.
-/

namespace BB6.Agent20.SpaceNeedleVariableValuation
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

theorem authentic_unbounded_feeder_valuation (t : Nat) :
    ∃ q v K : Nat,
      t < v ∧
      2*v = 9^(t+1)+3 ∧
      K+1 = 2*(t+1)*(v+1) ∧
      highLevelNext (.N (oddTower q v)) = some (.N (2^K-2)) := by
  obtain ⟨q,v,K,hgt,hv,hK,he⟩ :=
    NeedleVariableValuation.valuation_unbounded t
  have hmul : 0 < (t+1)*(v+1) :=
    Nat.mul_pos (by omega) (by omega)
  have hK1 : 1≤K := by
    rw [Nat.mul_assoc] at hK
    omega
  have he' : NeedleInverse.den v*q+NeedleInverse.bias v=(2:Nat)^K := by
    change (2^(v+1)+3)*q+3*2^v+v+3=(2:Nat)^K
    exact he.symm
  refine ⟨q,v,K,hgt,hv,hK,?_⟩
  exact BB6.Agent20.SpaceNeedleTriple.authentic_affine_successor
    q v K hK1 he'

#print axioms authentic_unbounded_feeder_valuation
end BB6.Agent20.SpaceNeedleVariableValuation

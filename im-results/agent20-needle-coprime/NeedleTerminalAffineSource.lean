import SpaceNeedleClosed
import NeedleGeneralInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleTriple
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

theorem authentic_affine_successor (q v K : Nat)
    (hK : 1≤K)
    (he : NeedleInverse.den v*q+NeedleInverse.bias v=(2:Nat)^K) :
    highLevelNext (.N (oddTower q v))=some (.N (2^K-2)) := by
  have hpow : 2≤(2:Nat)^K := by
    have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hK
    have hh : (2:Nat)^1=2 := by decide
    omega
  have hsub : (2:Nat)^K-2+2=(2:Nat)^K := Nat.sub_add_cancel hpow
  have heq : ((2:Nat)^K-2)+2 = NeedleInverse.den v*q+NeedleInverse.bias v := by
    rw [hsub]
    exact he.symm
  have htarget := (NeedleGeneralInverse.parent_successor_iff
    (oddTower q v) (2^K-2) q v (oddTower_factor q v)).mp heq
  exact (highLevelNext_iff_oddTower _ _).mpr ⟨q,v,rfl,htarget⟩

#print axioms authentic_affine_successor
end BB6.Agent20.SpaceNeedleTriple

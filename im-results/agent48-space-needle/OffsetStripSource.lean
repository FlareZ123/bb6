import OffsetStrip
import NeedleSharper
import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.OffsetStrip
open BB6.Agent48.Boundary
open BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Sharper unrestricted terminal-valuation ceiling for every authentic incoming source, except the known unique exception. -/
theorem source_stronger_valuation_bound (q v K : Nat)
    (hK : 1≤K)
    (h : highLevelNext (.N (oddTower q v))=some (.N (2^K-2))) :
    (q=61 ∧ v=6 ∧ K=13) ∨ 4*v≤K+2 := by
  have hpow : 2≤(2:Nat)^K := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hK
    omega
  have hsub : (2:Nat)^K-2+2=(2:Nat)^K := Nat.sub_add_cancel hpow
  have hn : highLevelNext (.N (oddTower q v))=
      some (.N (oddTower q v+v+3*(q+1))) :=
    (highLevelNext_iff_oddTower _ _).mpr ⟨q,v,rfl,rfl⟩
  have heval : oddTower q v+v+3*(q+1)=(2:Nat)^K-2 := by
    have he : (some (.N (oddTower q v+v+3*(q+1))) : Option HighLevelState) =
       some (.N (2^K-2)) := hn.symm.trans h
    simpa only [Option.some.injEq, HighLevelState.N.injEq] using he
  have hf := oddTower_factor q v
  have hpoly : (2:Nat)^v*(2*q+3)+v+3*(q+1)=(2:Nat)^K := by omega
  have heq : equation q v K := by
    unfold equation
    rw [model_eq]
    exact hpoly
  have hOriginal : NeedleInverse.equation q v K := by
    exact hpoly
  rcases NeedleSharper.sharper_valuation_bound q v K hOriginal with hex | hsharp
  · exact Or.inl hex
  · exact Or.inr (stronger_from_sharp q v K heq hsharp)

#print axioms source_stronger_valuation_bound
end BB6.Agent48.OffsetStrip

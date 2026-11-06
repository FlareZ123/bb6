import BoundaryExact
import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.Boundary
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- For the actual original Space Needle map, equality at its sharp linear terminal valuation wall occurs only twice. -/
theorem original_terminal_threshold_exact (q v K : Nat)
    (hK : K=3*v+3)
    (h : highLevelNext (.N (oddTower q v))=some (.N (2^K-2))) :
    (q=45 ∧ v=2 ∧ K=9) ∨ (q=214 ∧ v=3 ∧ K=12) := by
  have hkpos : 1 ≤ K := by omega
  have hpow : 2 ≤ (2:Nat)^K := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hkpos
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
  exact terminal_threshold_exact q v K heq hK

#print axioms original_terminal_threshold_exact
end BB6.Agent48.Boundary

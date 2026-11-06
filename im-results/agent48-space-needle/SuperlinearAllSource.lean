import SuperlinearAll
import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SuperModSource
open BB6.Agent48.SuperMod
open BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- For every positive slope c, each authentic one-step Space Needle
terminal feeder whose valuation exceeds 4*(3^c+1) has terminal exponent
strictly greater than c times that valuation. The quantified source state
is synthetic and need not be blank-reachable. -/
theorem original_terminal_superlinear (q v K c : Nat)
    (hc : 1≤c) (hv : 4*((3:Nat)^c+1)≤v) (hK : 1≤K)
    (h : highLevelNext (.N (oddTower q v))=some (.N (2^K-2))) :
    c*v<K := by
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
  exact terminal_superlinear_nat q v K c hc hv hpoly

#print axioms original_terminal_superlinear
end BB6.Agent48.SuperModSource

import Mathlib
import SpaceNeedleClosed
import AdjacentReflection

namespace BB6.Agent20AdjacentReflectionSource
open BB6.Agent20AdjacentReflection
open BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Signed affine source edge valid for *every* natural valuation,
    including v=0 and v=1 where a truncated Nat subtraction is wrong. -/
theorem source_signed_edge (v q e : Nat)
    (he : highLevelNext (.N (oddTower q v)) = some (.N e)) :
    ((2^(v+1) : Nat) : Int)*((e+2 : Nat) : Int) =
      ((2^(v+1)+3 : Nat) : Int)*((oddTower q v+2 : Nat) : Int) +
        ((2^v : Nat) : Int)*(2*(v : Int)-3) := by
  have hs : highLevelNext (.N (oddTower q v)) =
      some (.N (oddTower q v + v + 3*(q+1))) :=
    (highLevelNext_iff_oddTower _ _).mpr ⟨q,v,rfl,rfl⟩
  have heq : e = oddTower q v+v+3*(q+1) := by
    rw [hs] at he
    simp only [Option.some.injEq, HighLevelState.N.injEq] at he
    omega
  have heqN : e+2=(oddTower q v+2)+v+3*(q+1) := by omega
  have hfactor := oddTower_factor q v
  have heqI : ((e+2 : Nat) : Int) =
      ((oddTower q v+2 : Nat) : Int)+(v : Int)+3*((q : Int)+1) := by
    exact_mod_cast heqN
  have hfactorI : ((oddTower q v+2 : Nat) : Int) =
      ((2^v : Nat) : Int)*(2*(q : Int)+3) := by
    exact_mod_cast hfactor
  have hpow : ((2^(v+1) : Nat) : Int) = 2*((2^v : Nat) : Int) := by
    exact_mod_cast (show (2:Nat)^(v+1)=2*2^v by rw [pow_succ]; ring)
  push_cast
  rw [hpow]
  linear_combination (2*((2^v : Nat) : Int))*heqI - 3*hfactorI

/-- Original-source adjacent valuation reflection, including v=0 and v=1.
    The high-level map is the unchanged Cryptids machine definition. -/
theorem source_reflection_identity (v q e : Nat)
    (he : highLevelNext (.N (oddTower q v)) = some (.N e))
    (a : Int) :
    3*((3*((oddTower q v+2 : Nat) : Int)+a) +
       (3*((e+2 : Nat) : Int)+a) -
       2*(a-((2^v : Nat) : Int)*(2*(v : Int)-3))) =
      ((2^(v+2)+3 : Nat) : Int) *
       ((3*((e+2 : Nat) : Int)+a) -
        (3*((oddTower q v+2 : Nat) : Int)+a)) := by
  have h := source_signed_edge v q e he
  have hpow : ((2^(v+1)+3 : Nat) : Int) =
      ((2^(v+1) : Nat) : Int)+3 := by push_cast; ring
  rw [hpow] at h
  have hs := reflection_identity (a:=a) h
  have hscale : ((2^(v+2)+3 : Nat) : Int) =
      2*((2^(v+1) : Nat) : Int)+3 := by
    have hp : (2:Nat)^(v+2)=2*(2^(v+1)) := by
      rw [pow_succ]
      ring
    exact_mod_cast (by rw [hp]; ring : 2^(v+2)+3 = 2*(2^(v+1))+3)
  rw [hscale]
  exact hs

#print axioms source_signed_edge
#print axioms source_reflection_identity
end BB6.Agent20AdjacentReflectionSource

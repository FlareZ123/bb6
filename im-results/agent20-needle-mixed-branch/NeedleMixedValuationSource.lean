import SpaceNeedleClosed
import IndexPotential
import SpaceNeedlePotentialSource
import MixedValuationDisjoint
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20NeedleMixedSource
open BB6.Agent48.SpaceNeedle
open BB6.Agent20NeedlePotentialSource
open BB6.Agent20MixedValuation
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

private theorem exact_three_edge (q e : Nat)
    (he : highLevelNext (.N (oddTower q 3)) = some (.N e)) :
    16 * (e+2) = 19 * (oddTower q 3+2) + 24 := by
  have hs : highLevelNext (.N (oddTower q 3)) =
      some (.N (oddTower q 3 + 3 + 3*(q+1))) :=
    (highLevelNext_iff_oddTower _ _).mpr ⟨q,3,rfl,rfl⟩
  rw [hs] at he
  simp only [Option.some.injEq, HighLevelState.N.injEq] at he
  have ho := oddTower_factor q 3
  norm_num at ho
  omega

private theorem exact_five_edge (q e : Nat)
    (he : highLevelNext (.N (oddTower q 5)) = some (.N e)) :
    64 * (e+2) = 67 * (oddTower q 5+2) + 224 := by
  have hs : highLevelNext (.N (oddTower q 5)) =
      some (.N (oddTower q 5 + 5 + 3*(q+1))) :=
    (highLevelNext_iff_oddTower _ _).mpr ⟨q,5,rfl,rfl⟩
  rw [hs] at he
  simp only [Option.some.injEq, HighLevelState.N.injEq] at he
  have ho := oddTower_factor q 5
  norm_num at ho
  omega

/-- Original-source obstruction: if a prepared target admits valuation-3
    and valuation-5 predecessors, the valuation-3 parent cannot itself
    admit a valuation-5 predecessor. -/
theorem no_three_then_five_source (e q3 q5 q55 : Nat)
    (he3 : highLevelNext (.N (oddTower q3 3)) = some (.N e))
    (he5 : highLevelNext (.N (oddTower q5 5)) = some (.N e))
    (h55 : highLevelNext (.N (oddTower q55 5)) =
      some (.N (oddTower q3 3))) : False := by
  have ctarget : SourceChain 5 1 e (oddTower q5 5) :=
    SourceChain.step q5 he5 (SourceChain.zero _)
  have cparent : SourceChain 5 1 (oddTower q3 3) (oddTower q55 5) :=
    SourceChain.step q55 h55 (SourceChain.zero _)
  have target : 67 ∣ 3*(e+2)+224 := by
    simpa using allValuationsSource (w:=5) (by decide) ctarget
  have parent : 67 ∣ 3*(oddTower q3 3+2)+224 := by
    simpa using allValuationsSource (w:=5) (by decide) cparent
  exact (no_three_then_five (e+2) (oddTower q3 3+2)
    (exact_three_edge q3 e he3) target) parent

/-- The opposite order of switching is also impossible on genuine
    original-source high-level transitions. -/
theorem no_five_then_three_source (e q3 q5 q33 : Nat)
    (he3 : highLevelNext (.N (oddTower q3 3)) = some (.N e))
    (he5 : highLevelNext (.N (oddTower q5 5)) = some (.N e))
    (h33 : highLevelNext (.N (oddTower q33 3)) =
      some (.N (oddTower q5 5))) : False := by
  have ctarget : SourceChain 3 1 e (oddTower q3 3) :=
    SourceChain.step q3 he3 (SourceChain.zero _)
  have cparent : SourceChain 3 1 (oddTower q5 5) (oddTower q33 3) :=
    SourceChain.step q33 h33 (SourceChain.zero _)
  have target : 19 ∣ 3*(e+2)+24 := by
    simpa using allValuationsSource (w:=3) (by decide) ctarget
  have parent : 19 ∣ 3*(oddTower q5 5+2)+24 := by
    simpa using allValuationsSource (w:=3) (by decide) cparent
  exact (no_five_then_three (e+2) (oddTower q5 5+2)
    (exact_five_edge q5 e he5) target) parent

#print axioms no_three_then_five_source
#print axioms no_five_then_three_source
end BB6.Agent20NeedleMixedSource

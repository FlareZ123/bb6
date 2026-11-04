import SpaceNeedleClosed
import NeedleSharper
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleSharp
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Sharp source-connected valuation bound for every legitimate incoming
edge to a Space Needle original high-level terminal, with unique exception. -/
theorem original_terminal_sharper_bound (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    (q=61 ∧ v=6 ∧ k=12) ∨ 3*v+3 ≤ k+1 := by
  have hs := (predecessor_power_identity q v k).mp h
  have heq : NeedleInverse.equation q v (k+1) :=
    (NeedleInverse.original_source_equation_iff q v k).mpr hs
  have hb := NeedleSharper.sharper_valuation_bound q v (k+1) heq
  rcases hb with ⟨hq,hv,hK⟩ | hbound
  · exact Or.inl ⟨hq,hv,by omega⟩
  · exact Or.inr hbound

/-- Same sharp bound for arbitrary original-source immediate predecessor d. -/
theorem original_any_terminal_sharper_bound (d k : Nat)
    (h : highLevelNext (.N d) = some (.N (haltTower k))) :
    ∃ q v, d=oddTower q v ∧
      ((q=61 ∧ v=6 ∧ k=12) ∨ 3*v+3 ≤ k+1) := by
  obtain ⟨q,v,hd,_⟩ := (highLevelNext_iff_oddTower d (haltTower k)).mp h
  have he : highLevelNext (.N (oddTower q v)) =
      some (.N (haltTower k)) := by
    simpa only [hd] using h
  exact ⟨q,v,hd,original_terminal_sharper_bound q v k he⟩

#print axioms original_terminal_sharper_bound
#print axioms original_any_terminal_sharper_bound
end BB6.Agent20.SpaceNeedleSharp

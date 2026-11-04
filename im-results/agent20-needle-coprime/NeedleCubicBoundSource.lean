import SpaceNeedleClosed
import NeedleCubicBound
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleCubic
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Every original-source Space Needle halting feeder has valuation
v satisfying 3*v ≤ k+3, except the single exact (q,v,k)=(61,6,12). -/
theorem original_terminal_cubic_bound (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    (q=61 ∧ v=6 ∧ k=12) ∨ 3*v ≤ k+3 := by
  have hs := (predecessor_power_identity q v k).mp h
  have heq : NeedleInverse.equation q v (k+1) :=
    (NeedleInverse.original_source_equation_iff q v k).mpr hs
  have hb := NeedleCubicBound.cubic_valuation_bound q v (k+1) heq
  rcases hb with ⟨hq,hv,hK⟩ | hbound
  · exact Or.inl ⟨hq,hv,by omega⟩
  · exact Or.inr (by omega)

/-- Directly quantified over the original high-level source counter d. -/
theorem original_any_terminal_predecessor_cubic (d k : Nat)
    (h : highLevelNext (.N d) = some (.N (haltTower k))) :
    ∃ q v, d=oddTower q v ∧
      ((q=61 ∧ v=6 ∧ k=12) ∨ 3*v ≤ k+3) := by
  obtain ⟨q,v,hd,he⟩ := (highLevelNext_iff_oddTower d (haltTower k)).mp h
  have he' : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
    simpa only [hd] using h
  exact ⟨q,v,hd,original_terminal_cubic_bound q v k he'⟩

#print axioms original_terminal_cubic_bound
#print axioms original_any_terminal_predecessor_cubic
end BB6.Agent20.SpaceNeedleCubic

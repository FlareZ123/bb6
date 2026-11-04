import SpaceNeedleClosed
import NeedleCubicEnumerate

namespace BB6.Agent20.SpaceNeedleCubicEnumeration
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- An executable finite list of ALL genuine one-step terminal feeders
in the pinned original Space Needle acceleration, at cubic valuation cutoff. -/
theorem original_terminal_cubic_list_iff (q v k : Nat) :
    (v,q) ∈ NeedleCubicEnum.cubicParents (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [NeedleCubicEnum.cubicParents_spec]
  rw [NeedleInverse.original_source_equation_iff]
  exact (predecessor_power_identity q v k).symm

/-- The original source directly has a feeder exactly when the finite
cubic list contains a witness matching that source. -/
theorem original_any_terminal_cubic_list (d k : Nat) :
    highLevelNext (.N d) = some (.N (haltTower k)) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ NeedleCubicEnum.cubicParents (k+1) := by
  constructor
  · intro hh
    obtain ⟨q,v,hd,_⟩ :=
      (highLevelNext_iff_oddTower d (haltTower k)).mp hh
    have hh' : highLevelNext (.N (oddTower q v)) =
        some (.N (haltTower k)) := by
      simpa only [hd] using hh
    exact ⟨q,v,hd,(original_terminal_cubic_list_iff q v k).mpr hh'⟩
  · rintro ⟨q,v,hd,hlist⟩
    have hh := (original_terminal_cubic_list_iff q v k).mp hlist
    simpa only [hd] using hh

#print axioms original_terminal_cubic_list_iff
#print axioms original_any_terminal_cubic_list
end BB6.Agent20.SpaceNeedleCubicEnumeration

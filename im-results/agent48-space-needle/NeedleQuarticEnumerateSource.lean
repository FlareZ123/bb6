import SpaceNeedleClosed
import NeedleQuarticEnumerate

namespace BB6.Agent48.SpaceNeedleQuarticEnumeration
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- The exact quartic-bounded list of every valid original-machine feeder
of a halting tower, for every natural index k. -/
theorem original_terminal_quartic_list_iff (q v k : Nat) :
    (v,q) ∈ NeedleQuarticEnum.quarticParents (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [NeedleQuarticEnum.quarticParents_spec]
  rw [NeedleInverse.original_source_equation_iff]
  exact (predecessor_power_identity q v k).symm

/-- Source-complete terminal inverse enumeration for every counter d,
using the actual pinned high-level transition and genuine halt destination. -/
theorem original_any_terminal_quartic_list (d k : Nat) :
    highLevelNext (.N d) = some (.N (haltTower k)) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ NeedleQuarticEnum.quarticParents (k+1) := by
  constructor
  · intro hh
    obtain ⟨q,v,hd,_⟩ :=
      (highLevelNext_iff_oddTower d (haltTower k)).mp hh
    have hh' : highLevelNext (.N (oddTower q v)) =
        some (.N (haltTower k)) := by
      simpa only [hd] using hh
    exact ⟨q,v,hd,(original_terminal_quartic_list_iff q v k).mpr hh'⟩
  · rintro ⟨q,v,hd,hlist⟩
    have hh := (original_terminal_quartic_list_iff q v k).mp hlist
    simpa only [hd] using hh

#print axioms original_terminal_quartic_list_iff
#print axioms original_any_terminal_quartic_list
end BB6.Agent48.SpaceNeedleQuarticEnumeration

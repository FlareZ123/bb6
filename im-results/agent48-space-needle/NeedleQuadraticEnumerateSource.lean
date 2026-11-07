import SpaceNeedleClosed
import NeedleQuadraticEnumerate

namespace BB6.Agent48.SpaceNeedleQuadraticEnumeration
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- The quadratic finite list is an exact inverse of every one-step
    predecessor of the original pinned Space Needle terminal state. -/
theorem original_terminal_quadratic_list_iff (q v k : Nat) :
    (v,q) ∈ NeedleQuadraticEnum.quadraticParents (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [NeedleQuadraticEnum.quadraticParents_spec]
  rw [NeedleInverse.original_source_equation_iff q v k]
  exact (predecessor_power_identity q v k).symm

/-- The sixth-regular filtered list is source-exact as well. The
    terminal exponent in the arithmetic equation is k+1. -/
theorem original_terminal_quadratic_regular_list_iff (q v k : Nat) :
    (v,q) ∈ NeedleQuadraticEnum.quadraticRegularParents (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) ∧
        6*v≤k+5 := by
  rw [NeedleQuadraticEnum.quadraticRegularParents_spec]
  rw [NeedleInverse.original_source_equation_iff q v k]
  constructor
  · rintro ⟨hfeed,hbound⟩
    exact ⟨(predecessor_power_identity q v k).mpr hfeed,hbound⟩
  · rintro ⟨hsource,hbound⟩
    exact ⟨(predecessor_power_identity q v k).mp hsource,hbound⟩

/-- Every original-source terminal feeder is represented by the quadratic
    list, and every list entry is an actual source predecessor. -/
theorem original_any_terminal_quadratic_list (d k : Nat) :
    highLevelNext (.N d) = some (.N (haltTower k)) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ NeedleQuadraticEnum.quadraticParents (k+1) := by
  constructor
  · intro hh
    obtain ⟨q,v,hd,_⟩ :=
      (highLevelNext_iff_oddTower d (haltTower k)).mp hh
    have hh' : highLevelNext (.N (oddTower q v)) =
        some (.N (haltTower k)) := by
      simpa only [hd] using hh
    exact ⟨q,v,hd,(original_terminal_quadratic_list_iff q v k).mpr hh'⟩
  · rintro ⟨q,v,hd,hlist⟩
    have hh := (original_terminal_quadratic_list_iff q v k).mp hlist
    simpa only [hd] using hh

#print axioms original_terminal_quadratic_list_iff
#print axioms original_terminal_quadratic_regular_list_iff
#print axioms original_any_terminal_quadratic_list
end BB6.Agent48.SpaceNeedleQuadraticEnumeration

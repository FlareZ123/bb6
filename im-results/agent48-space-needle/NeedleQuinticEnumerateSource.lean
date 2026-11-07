import SpaceNeedleClosed
import NeedleQuinticEnumerate

namespace BB6.Agent48.SpaceNeedleQuinticEnumeration
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Full original-source equivalence for every one-step terminal feeder. -/
theorem original_terminal_quintic_list_iff (q v k : Nat) :
    (v,q) ∈ NeedleQuinticEnum.quinticParents (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [NeedleQuinticEnum.quinticParents_spec]
  rw [NeedleInverse.original_source_equation_iff]
  exact (predecessor_power_identity q v k).symm

/-- Complete source-exact terminal predecessor list, without a finite exponent cutoff. -/
theorem original_any_terminal_quintic_list (d k : Nat) :
    highLevelNext (.N d) = some (.N (haltTower k)) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ NeedleQuinticEnum.quinticParents (k+1) := by
  constructor
  · intro hh
    obtain ⟨q,v,hd,_⟩ :=
      (highLevelNext_iff_oddTower d (haltTower k)).mp hh
    have hh' : highLevelNext (.N (oddTower q v)) =
        some (.N (haltTower k)) := by
      simpa only [hd] using hh
    exact ⟨q,v,hd,(original_terminal_quintic_list_iff q v k).mpr hh'⟩
  · rintro ⟨q,v,hd,hlist⟩
    have hh := (original_terminal_quintic_list_iff q v k).mp hlist
    simpa only [hd] using hh

#print axioms original_terminal_quintic_list_iff
#print axioms original_any_terminal_quintic_list
end BB6.Agent48.SpaceNeedleQuinticEnumeration

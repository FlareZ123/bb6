import SpaceNeedleClosed
import SuperlinearEnumerate

namespace BB6.Agent48.SuperlinearSourceEnum
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Every legal terminal feeder of the unchanged original Space Needle map
occurs in the finite all-slope list, and every listed feeder is source-valid. -/
theorem original_terminal_superlinear_list_iff (q v k c : Nat) (hc : 1≤c) :
    (v,q) ∈ BB6.Agent48.SuperlinearEnum.superlinearParents (k+1) c ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [BB6.Agent48.SuperlinearEnum.superlinearParents_spec q v (k+1) c hc]
  rw [NeedleInverse.original_source_equation_iff]
  exact (predecessor_power_identity q v k).symm

/-- Complete original-machine one-step terminal inverse, uniformly for
every terminal index k and every selected positive all-slope parameter c. -/
theorem original_any_terminal_superlinear_list (d k c : Nat) (hc : 1≤c) :
    highLevelNext (.N d) = some (.N (haltTower k)) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ BB6.Agent48.SuperlinearEnum.superlinearParents (k+1) c := by
  constructor
  · intro hh
    obtain ⟨q,v,hd,_⟩ :=
      (highLevelNext_iff_oddTower d (haltTower k)).mp hh
    have hh' : highLevelNext (.N (oddTower q v)) =
        some (.N (haltTower k)) := by
      simpa only [hd] using hh
    exact ⟨q,v,hd,(original_terminal_superlinear_list_iff q v k c hc).mpr hh'⟩
  · rintro ⟨q,v,hd,hlist⟩
    have hh := (original_terminal_superlinear_list_iff q v k c hc).mp hlist
    simpa only [hd] using hh

#print axioms original_terminal_superlinear_list_iff
#print axioms original_any_terminal_superlinear_list
end BB6.Agent48.SuperlinearSourceEnum

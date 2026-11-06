import SpaceNeedleClosed
import SuperlinearOptimized

namespace BB6.Agent48.SuperlinearOptimizedSource
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Fully automatic, optimally selected positive-slope valuation cutoff,
verified for every one-step terminal feeder of the pinned original map. -/
theorem original_optimized_terminal_iff (q v k : Nat) :
    (v,q) ∈ BB6.Agent48.SuperlinearOptimal.optimizedParents (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [BB6.Agent48.SuperlinearOptimal.optimizedParents_spec]
  rw [NeedleInverse.original_source_equation_iff]
  exact (predecessor_power_identity q v k).symm

/-- The optimized, automatically selected list exhausts all and only
source-valid terminal feeders from arbitrary genuine original counters d. -/
theorem original_any_optimized_terminal (d k : Nat) :
    highLevelNext (.N d) = some (.N (haltTower k)) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ BB6.Agent48.SuperlinearOptimal.optimizedParents (k+1) := by
  constructor
  · intro hh
    obtain ⟨q,v,hd,_⟩ :=
      (highLevelNext_iff_oddTower d (haltTower k)).mp hh
    have hh' : highLevelNext (.N (oddTower q v)) =
        some (.N (haltTower k)) := by
      simpa only [hd] using hh
    exact ⟨q,v,hd,(original_optimized_terminal_iff q v k).mpr hh'⟩
  · rintro ⟨q,v,hd,hlist⟩
    have hh := (original_optimized_terminal_iff q v k).mp hlist
    simpa only [hd] using hh

#print axioms original_optimized_terminal_iff
#print axioms original_any_optimized_terminal
end BB6.Agent48.SuperlinearOptimizedSource

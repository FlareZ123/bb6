import NeedleRootCubic
import SuperlinearOptimized

namespace BB6.Agent48.SpaceNeedleRootOptimal
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- A genuine blank-root equivalence: the original raw six-state machine
halts iff some authentic blank-reached high-level counter belongs to the
fully exhaustive, automatically minimized terminal predecessor list.
This does not resolve the unbounded existential over K or blank reachability. -/
theorem raw_halts_iff_reaches_optimized_feeder :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ BB6.Agent48.SuperlinearOptimal.optimizedParents (k+1) := by
  rw [BB6.Agent20.SpaceNeedleRootCubic.raw_halts_iff_reaches_cubic_feeder]
  constructor
  · rintro ⟨k,q,v,hr,hl⟩
    have he := (NeedleCubicEnum.cubicParents_spec q v (k+1)).mp hl
    exact ⟨k,q,v,hr,(BB6.Agent48.SuperlinearOptimal.optimizedParents_spec q v (k+1)).mpr he⟩
  · rintro ⟨k,q,v,hr,hl⟩
    have he := (BB6.Agent48.SuperlinearOptimal.optimizedParents_spec q v (k+1)).mp hl
    exact ⟨k,q,v,hr,(NeedleCubicEnum.cubicParents_spec q v (k+1)).mpr he⟩

#print axioms raw_halts_iff_reaches_optimized_feeder
end BB6.Agent48.SpaceNeedleRootOptimal

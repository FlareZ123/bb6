import NeedleRootCubic
import NeedleQuadraticEnumerateSource

namespace BB6.Agent48.SpaceNeedleRootQuadratic
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open NeedleQuadraticEnum

/-- The authentic raw machine halts exactly when its blank-root orbit reaches
    a member of the complete square-root/logarithmic terminal feeder list.
    This is a lossless reduction of the unbounded halting question, not a
    decision of the remaining reachability existential. -/
theorem raw_halts_iff_reaches_quadratic_feeder :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ quadraticParents (k+1) := by
  rw [BB6.Agent20.SpaceNeedleRootCubic.raw_halts_iff_reaches_cubic_feeder]
  constructor
  · rintro ⟨k,q,v,hr,hcubic⟩
    have heq := (NeedleCubicEnum.cubicParents_spec q v (k+1)).mp hcubic
    exact ⟨k,q,v,hr,(quadraticParents_spec q v (k+1)).mpr heq⟩
  · rintro ⟨k,q,v,hr,hquadratic⟩
    have heq := (quadraticParents_spec q v (k+1)).mp hquadratic
    exact ⟨k,q,v,hr,(NeedleCubicEnum.cubicParents_spec q v (k+1)).mpr heq⟩

#print axioms raw_halts_iff_reaches_quadratic_feeder
end BB6.Agent48.SpaceNeedleRootQuadratic

import NeedleSixthRoot
import NeedleQuadraticEnumerate

namespace BB6.Agent48.SpaceNeedleRootQuadraticRegular
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open NeedleQuadraticEnum

/-- The original blank-start raw machine halts exactly when its orbit reaches
    a feeder in the square-root/logarithmic list, intersected with the
    already certified sixth-linear root restriction. The terminal exponent
    remains unbounded, so this is a sharper reduction rather than a decision. -/
theorem raw_halts_iff_reaches_quadratic_regular_feeder :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ quadraticRegularParents (k+1) := by
  rw [BB6.Agent48.SpaceNeedleSixthRoot.raw_halts_iff_reaches_sixth_regular]
  constructor
  · rintro ⟨k,q,v,hr,h6⟩
    have h6spec := (NeedleSixthRegular.parents_spec q v (k+1)).mp h6
    exact ⟨k,q,v,hr,
      (quadraticRegularParents_spec q v (k+1)).mpr h6spec⟩
  · rintro ⟨k,q,v,hr,hquadratic⟩
    have hquadraticSpec :=
      (quadraticRegularParents_spec q v (k+1)).mp hquadratic
    exact ⟨k,q,v,hr,
      (NeedleSixthRegular.parents_spec q v (k+1)).mpr hquadraticSpec⟩

#print axioms raw_halts_iff_reaches_quadratic_regular_feeder
end BB6.Agent48.SpaceNeedleRootQuadraticRegular

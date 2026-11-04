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
  rw [highLevelNext_iff_oddTower]
  constructor
  · rintro ⟨q,v,hd,he⟩
    refine ⟨q,v,hd,?_⟩
    apply (original_terminal_cubic_list_iff q v k).mpr
    apply (highLevelNext_iff_oddTower (oddTower q v) (haltTower k)).mpr
    exact ⟨q,v,rfl,by simpa only [hd] using he⟩
  · rintro ⟨q,v,hd,hlist⟩
    refine ⟨q,v,hd,?_⟩
    have hs := (original_terminal_cubic_list_iff q v k).mp hlist
    obtain ⟨q',v',heq,hsucc⟩ :=
      (highLevelNext_iff_oddTower (oddTower q v) (haltTower k)).mp hs
    rw [hd] at heq
    -- The equality is only used to substitute the original matched source.
    subst d
    exact hsucc

#print axioms original_terminal_cubic_list_iff
#print axioms original_any_terminal_cubic_list
end BB6.Agent20.SpaceNeedleCubicEnumeration

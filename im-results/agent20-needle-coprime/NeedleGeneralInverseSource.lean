import SpaceNeedleClosed
import NeedleGeneralInverse

namespace BB6.Agent20.SpaceNeedleGeneralInverse
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- A complete executable inverse of EVERY successful original high-level
Space Needle transition, without a power-of-two target restriction. -/
theorem original_source_inverse_iff (d e : Nat) :
    highLevelNext (.N d) = some (.N e) ↔
      ∃ q v, d=oddTower q v ∧
        (v,q) ∈ NeedleGeneralInverse.parents (e+2) := by
  rw [highLevelNext_iff_oddTower]
  constructor
  · rintro ⟨q,v,hd,he⟩
    refine ⟨q,v,hd,?_⟩
    have hf := oddTower_factor q v
    apply (NeedleGeneralInverse.parents_spec q v (e+2)).mpr
    apply (NeedleGeneralInverse.parent_successor_iff (oddTower q v) e q v hf).mpr
    simpa only [hd] using he
  · rintro ⟨q,v,hd,hpair⟩
    refine ⟨q,v,hd,?_⟩
    have hf := oddTower_factor q v
    have hp := (NeedleGeneralInverse.parents_spec q v (e+2)).mp hpair
    have he := (NeedleGeneralInverse.parent_successor_iff
       (oddTower q v) e q v hf).mp hp
    simpa only [hd] using he

#print axioms original_source_inverse_iff
end BB6.Agent20.SpaceNeedleGeneralInverse

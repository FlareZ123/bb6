import SheepSourceBridge
import SectionExclusionBridge

namespace BB6.Agent22.SheepSourceExclusions
open BusyBeaver

/-- All time blank-tape halting in original six-state machine is equivalent
to reaching a nonexcluded power under the exact return graph. The 157 of 360
excluded exponent classes are the existing fully certified Agent 16 theorem. -/
theorem raw_halts_iff_nonexcluded_power :
    IsHalt BB6.Agent22.SheepSource.Source.target ↔
    ∃ j : Nat, 2 ≤ j ∧ ¬ SheepInverse.PeriodicExcluded j ∧
      BB6.Agent22.Sheep.Reach 5 (2^j) := by
  constructor
  · intro hraw
    obtain ⟨j,hj,hr⟩ :=
      BB6.Agent22.SheepSource.raw_halts_iff_power.mp hraw
    refine ⟨j,hj,?_,hr⟩
    intro hex
    exact (BB6.Agent22.SectionExclusionBridge.excluded_power_unreachable j hex) hr
  · rintro ⟨j,hj,_,hr⟩
    exact BB6.Agent22.SheepSource.raw_halts_iff_power.mpr ⟨j,hj,hr⟩

#print axioms BB6.Agent22.SheepSourceExclusions.raw_halts_iff_nonexcluded_power
end BB6.Agent22.SheepSourceExclusions

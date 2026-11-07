import StrongMassOriginal
import FastRootBackward

namespace BB6.Agent3StrongMass

/-- A sound original-source fixed-target decider with a sharper fuel, derived from exact mass growth. -/
theorem backwardFast_quarter_iff (x y : Nat) :
    BB6.Agent11Fast.backwardFast ((x+2*y-7)/4) (x,y) = true ↔
      BB6.Agent11Mass.SectionReach x y := by
  simpa using
    (BB6.Agent11Fast.backwardFast_iff ((x+2*y-7)/4) (x,y)).trans
      (section_reach_iff_quarter_bound x y).symm

#print axioms backwardFast_quarter_iff
end BB6.Agent3StrongMass

import StrongMassOriginal
import FastRootFuel

namespace BB6.Agent3StrongMass

/-- A sound original-source fixed-target decider with a sharper fuel, derived from exact mass growth. -/
theorem backwardFast_quarter_iff (x y : Nat) :
    BB6.Agent11Fast.backwardFast ((x+2*y-7)/4) (x,y) = true ↔
      BB6.Agent11Mass.SectionReach x y := by
  simpa using
    (BB6.Agent11Fast.backwardFast_iff ((x+2*y-7)/4) (x,y)).trans
      (section_reach_iff_quarter_bound x y).symm

/-- Kernel-evaluable original-source quarter-fuel Boolean, with a proven all-time equivalence. -/
def quarterFuelRootDecision (x y : Nat) : Bool :=
  BB6.Agent11Fast.backwardFastFuel ((x+2*y-7)/4) (x,y)

theorem quarterFuelRootDecision_iff (x y : Nat) :
    quarterFuelRootDecision x y = true ↔
      BB6.Agent11Mass.SectionReach x y := by
  unfold quarterFuelRootDecision
  rw [BB6.Agent11Fast.backwardFastFuel_eq]
  exact backwardFast_quarter_iff x y

#print axioms quarterFuelRootDecision_iff
#print axioms backwardFast_quarter_iff
end BB6.Agent3StrongMass

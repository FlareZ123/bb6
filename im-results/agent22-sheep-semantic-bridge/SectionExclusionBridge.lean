import Reach
import SheepPowerBridge

namespace BB6.Agent22.SectionExclusionBridge

open BB6.Agent22.Sheep

/-- Each genuine section edge is identically an Agent 16 certified return edge. -/
theorem step_identical {t v : Nat} (h : SheepBridge.SectionNext t v) :
    SheepInverse.Step t v := by
  cases h with
  | triple a =>
    simpa [SheepInverse.Special, Nat.mul_comm] using SheepInverse.Step.special a
  | general a u hu hodd =>
    simpa [SheepInverse.Generic] using SheepInverse.Step.generic a u hodd hu

/-- Starting at an old reachable section state, every new path remains reachable
in the original exact Agent 16 return graph. -/
theorem to_old_reach {t v : Nat} (h : Reach t v)
    (ht : SheepInverse.Reach t) : SheepInverse.Reach v := by
  induction h with
  | refl _ => exact ht
  | cons hedge htail ih =>
    exact ih (SheepInverse.Reach.successor ht (step_identical hedge))

/-- Relate the independently machine-certified blank-section return graph to
Agent 16's formally excluded families. -/
theorem old_reach_from_blank {t : Nat} (h : Reach 5 t) :
    SheepInverse.Reach t :=
  to_old_reach h SheepInverse.Reach.initial

/-- All existing Agent 16 exclusions are actual unreachability claims in
our machine-level-certified return relation. -/
theorem excluded_power_unreachable (j : Nat)
    (hj : SheepInverse.PeriodicExcluded j) : ¬ Reach 5 (2^j) := by
  intro hr
  have ho := old_reach_from_blank hr
  exact (SheepInverse.periodic_power_unreachable j hj (2^j) ho) rfl

#print axioms BB6.Agent22.SectionExclusionBridge.step_identical
#print axioms BB6.Agent22.SectionExclusionBridge.excluded_power_unreachable
end BB6.Agent22.SectionExclusionBridge

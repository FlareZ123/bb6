import ModularConeHighStopCriterion

set_option maxHeartbeats 4000000

namespace BB6.Agent11ModularStrictness

open BB6.Agent42ModularCone

/-- The concrete high-stop point (j,m)=(20,3) survives the pre-existing
    exact highAllowed predicate. -/
theorem old_high_allowed_20_3 :
    BB6.Agent11SixAll.highAllowed 20 3 := by
  decide

/-- The modular inverse-cone checker rejects the unified point (J,m)=(21,3). -/
theorem modular_high_stop_excluded_21_3 :
    highStopExcluded 21 3 = true := by
  decide

/-- The new modular conjunct strictly narrows the old highAllowed set. -/
theorem high_allowed_modular_rejects_20_3 :
    ¬ highAllowedModular 20 3 := by
  simp [highAllowedModular, old_high_allowed_20_3,
    modular_high_stop_excluded_21_3]

/-- Strictness witness: the old predicate accepts the point, while the
    source-connected modular cone proves its CReach target impossible. -/
theorem modular_filter_strict_witness_20_3 :
    BB6.Agent11SixAll.highAllowed 20 3 ∧
      ¬ highAllowedModular 20 3 ∧
      ¬ BB6.Agent3.CReach 43 5854 := by
  exact ⟨old_high_allowed_20_3,
    high_allowed_modular_rejects_20_3,
    BB6.Agent42ModularCone.high_stop_example_21_3⟩

#print axioms old_high_allowed_20_3
#print axioms modular_high_stop_excluded_21_3
#print axioms high_allowed_modular_rejects_20_3
#print axioms modular_filter_strict_witness_20_3

end BB6.Agent11ModularStrictness

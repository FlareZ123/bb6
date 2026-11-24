import ModularConeFullCriterion

set_option maxHeartbeats 4000000

namespace BB6.Agent11ModularStrictness

open BB6.Agent42ModularCone

/-- The current full Boolean/phase high predicate admits the candidate
    before adding the modular inverse-cone conjunct. -/
theorem full_bool_high_allowed_20_3 :
    BB6.Agent27FullBool.highAllowedFullBool 20 3 = true := by
  decide

/-- The modular inverse-cone checker rejects the unified point (J,m)=(21,3). -/
theorem modular_high_stop_excluded_21_3 :
    highStopExcluded 21 3 = true := by
  decide

/-- The C70 high rectangles do not already remove this point. -/
theorem c70_allows_20_3 :
    ¬((20 % 128 = 63 ∧ 3 % 128 = 82) ∨
      (20 % 128 = 127 ∧ 3 % 128 = 18)) := by
  decide

/-- The full pre-modular high parameter predicate accepts this point. -/
theorem full_pre_modular_accepts_20_3 :
    BB6.Agent27FullBool.highAllowedFullBool 20 3 = true ∧
      ¬((20 % 128 = 63 ∧ 3 % 128 = 82) ∨
        (20 % 128 = 127 ∧ 3 % 128 = 18)) :=
  ⟨full_bool_high_allowed_20_3, c70_allows_20_3⟩

/-- The new modular conjunct strictly narrows the full Boolean/phase+C70
    high predicate, if the concrete full Boolean decision above is accepted. -/
theorem full_modular_rejects_20_3 :
    ¬ highAllowedFullModular 20 3 := by
  simp [highAllowedFullModular, full_bool_high_allowed_20_3,
    c70_allows_20_3, modular_high_stop_excluded_21_3]

/-- Strictness witness paired with the source-connected non-reachability
    theorem for CReach(43,5854). -/
theorem full_modular_strict_witness_20_3 :
    full_pre_modular_accepts_20_3 ∧
      ¬ highAllowedFullModular 20 3 ∧
      ¬ BB6.Agent3.CReach 43 5854 := by
  exact ⟨full_pre_modular_accepts_20_3,
    full_modular_rejects_20_3,
    BB6.Agent42ModularCone.high_stop_example_21_3⟩

#print axioms full_bool_high_allowed_20_3
#print axioms modular_high_stop_excluded_21_3
#print axioms full_modular_rejects_20_3
#print axioms full_modular_strict_witness_20_3

end BB6.Agent11ModularStrictness

import ModularConeFullCriterion

set_option maxHeartbeats 4000000

namespace BB6.Agent11ModularStrictness

open BB6.Agent42ModularCone

/-- The full Boolean/phase high predicate admits the C58 all-depth
    residue-family representative (j,m)=(215,3) before modular filtering. -/
theorem full_bool_high_allowed_215_3 :
    BB6.Agent27FullBool.highAllowedFullBool 215 3 = true := by
  decide

/-- The modular inverse-cone checker rejects the unified point (J,m)=(216,3). -/
theorem modular_high_stop_excluded_216_3 :
    highStopExcluded 216 3 = true := by
  decide

/-- The C70 high rectangles do not already remove this point. -/
theorem c70_allows_215_3 :
    ¬((215 % 128 = 63 ∧ 3 % 128 = 82) ∨
      (215 % 128 = 127 ∧ 3 % 128 = 18)) := by
  decide

/-- The full pre-modular high parameter predicate accepts this point. -/
theorem full_pre_modular_accepts_215_3 :
    BB6.Agent27FullBool.highAllowedFullBool 215 3 = true ∧
      ¬((215 % 128 = 63 ∧ 3 % 128 = 82) ∨
        (215 % 128 = 127 ∧ 3 % 128 = 18)) :=
  ⟨full_bool_high_allowed_215_3, c70_allows_215_3⟩

/-- The new modular conjunct strictly narrows the full Boolean/phase+C70
    high predicate. -/
theorem full_modular_rejects_215_3 :
    ¬ highAllowedFullModular 215 3 := by
  simp [highAllowedFullModular, full_bool_high_allowed_215_3,
    c70_allows_215_3, modular_high_stop_excluded_216_3]

/-- Strictness witness paired with the source-connected non-reachability
    theorem for CReach(433,55579). The high-stop equation is exact:
    55579 + 216 + 3*3 + 4 = 2^8 * 218. -/
theorem full_modular_strict_witness_215_3 :
    full_pre_modular_accepts_215_3 ∧
      ¬ highAllowedFullModular 215 3 ∧
      ¬ BB6.Agent3.CReach 433 55579 := by
  have hx : 433 = 2 * 216 + 1 := by decide
  have hstop : 55579 + 216 + 3 * 3 + 4 =
      2 ^ (2 * 3 + 2) * (216 + 2) := by decide
  exact ⟨full_pre_modular_accepts_215_3,
    full_modular_rejects_215_3,
    high_stop_excluded hx hstop modular_high_stop_excluded_216_3⟩

#print axioms full_bool_high_allowed_215_3
#print axioms modular_high_stop_excluded_216_3
#print axioms full_modular_rejects_215_3
#print axioms full_modular_strict_witness_215_3

end BB6.Agent11ModularStrictness

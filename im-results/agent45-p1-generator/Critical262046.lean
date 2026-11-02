import Quarter262046
import GeneralQuarterBridge2
import GeneralQuarterBound

namespace BB6.Agent45Quarter262046

/-- Infinite authentic P1 blank-critical exclusion at shifted quarter residue 262046. -/
theorem no_critical_262046 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(262144*q+262046)-2*(262144*q+262046)-10) := by
  exact BB6.Agent45Quarter2.critical_of_quarter_hub_shift2 262046 q
    (by decide) (by decide) (by decide)
    (BB6.Agent45Quarter.quarter_exponent_bound 262046 q (by decide))
    (by simpa using BB6.Agent45Generator.no_hub_262046 q)

#print axioms BB6.Agent45Quarter262046.no_critical_262046
end BB6.Agent45Quarter262046

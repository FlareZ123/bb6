import Quarter262078
import GeneralQuarterBridge2
import GeneralQuarterBound

namespace BB6.Agent45Quarter262078

/-- Infinite authentic P1 blank-critical exclusion at shifted quarter residue 262078. -/
theorem no_critical_262078 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(262144*q+262078)-2*(262144*q+262078)-10) := by
  exact BB6.Agent45Quarter2.critical_of_quarter_hub_shift2 262078 q
    (by decide) (by decide) (by decide)
    (BB6.Agent45Quarter.quarter_exponent_bound 262078 q (by decide))
    (by simpa using BB6.Agent45Generator.no_hub_262078 q)

#print axioms BB6.Agent45Quarter262078.no_critical_262078
end BB6.Agent45Quarter262078

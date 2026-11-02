import Quarter262114Final
import GeneralQuarterBridge2
import GeneralQuarterBound

namespace BB6.Agent45Quarter262114

/-- Universal authentic blank-P1 critical exclusion, n = 262144*q+262114.
The shifted K=2 cone is certified by 23 exact G-inverse nodes. -/
theorem no_critical_262114 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(262144*q+262114)-2*(262144*q+262114)-10) := by
  exact BB6.Agent45Quarter2.critical_of_quarter_hub_shift2 262114 q
    (by decide) (by decide) (by decide)
    (BB6.Agent45Quarter.quarter_exponent_bound 262114 q (by decide))
    (by simpa using BB6.Agent45Quarter262114.no_hub_262114 q)

#print axioms BB6.Agent45Quarter262114.no_critical_262114
end BB6.Agent45Quarter262114

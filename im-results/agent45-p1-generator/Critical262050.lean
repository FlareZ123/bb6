import Quarter262050Final
import GeneralQuarterBridge2
import GeneralQuarterBound

namespace BB6.Agent45Quarter262050

/-- Universal authentic blank-P1 critical exclusion, n=262144*q+262050.
Entire inverse cone is source-checked by 23 parametric exact-G predecessor cases. -/
theorem no_critical_262050 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(262144*q+262050)-2*(262144*q+262050)-10) := by
  exact BB6.Agent45Quarter2.critical_of_quarter_hub_shift2 262050 q
    (by decide) (by decide) (by decide)
    (BB6.Agent45Quarter.quarter_exponent_bound 262050 q (by decide))
    (by simpa using BB6.Agent45Quarter262050.no_hub_262050 q)

#print axioms BB6.Agent45Quarter262050.no_critical_262050
end BB6.Agent45Quarter262050

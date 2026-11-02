import Quarter262130
import GeneralQuarterBridge2
import GeneralQuarterBound

namespace BB6.Agent45Quarter262130

/-- An authentic P1 blank-orbit exclusion of one of the 21 quarter classes
    that require the safer t=s-2 parameter shift. -/
theorem no_critical_262130 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(262144*q+262130)-2*(262144*q+262130)-10) := by
  exact BB6.Agent45Quarter2.critical_of_quarter_hub_shift2 262130 q
    (by decide) (by decide) (by decide)
    (BB6.Agent45Quarter.quarter_exponent_bound 262130 q (by decide))
    (by simpa using BB6.Agent45Generator.no_hub_262130 q)

#print axioms BB6.Agent45Quarter262130.no_critical_262130
end BB6.Agent45Quarter262130

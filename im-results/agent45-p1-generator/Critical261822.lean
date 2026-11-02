import Quarter261822
import GeneralQuarterBridge2
import GeneralQuarterBound

namespace BB6.Agent45Quarter261822

/-- Full original-source blank-P1 critical exclusion from the K2 inverse cone
at the independent high residue r=261822. -/
theorem no_critical_261822 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(262144*q+261822)-2*(262144*q+261822)-10) := by
  exact BB6.Agent45Quarter2.critical_of_quarter_hub_shift2 261822 q
    (by decide) (by decide) (by decide)
    (BB6.Agent45Quarter.quarter_exponent_bound 261822 q (by decide))
    (by simpa using BB6.Agent45Generator.no_hub_261822 q)

#print axioms BB6.Agent45Quarter261822.no_critical_261822
end BB6.Agent45Quarter261822

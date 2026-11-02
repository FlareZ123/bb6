import Quarter174Final
import GeneralQuarterBridge

namespace BB6.Agent45Quarter174
/-- Instance of the all-residue semantic bridge for the new first quarter class. -/
theorem no_critical_174_via_generic (q : Nat) :
    ¬ BB6.Agent1.Reach 2 (14*2^(262144*q+174)-2*(262144*q+174)-10) := by
  exact BB6.Agent45Quarter.critical_of_quarter_hub 174 q
    (by decide) (by decide) (by decide)
    (Y_bound_174 q)
    (by simpa using no_hub_174 q)

#print axioms BB6.Agent45Quarter174.no_critical_174_via_generic
end BB6.Agent45Quarter174

import Q41Finite
import UniformUniversalCylinder

namespace BB6.Agent9Q41

/-- An original blank-root P1 critical-gateway exclusion for every
    q=41+2^51*r, in particular the previously uncovered exponent n=658. -/
theorem blank_no_critical_658_plus_2pow55 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(41+2^(10+41)*r)+2) -
       2*(16*(41+2^(10+41)*r)+2)-10) := by
  exact BB6.Agent9UniformUniversal.universal_blank_critical_cylinder
    41 (by decide)
    nodes0 nodes1 root0 root1 closed0 closed1
    small0 small1 no1024_0 no1024_1 r

#print axioms blank_no_critical_658_plus_2pow55
end BB6.Agent9Q41

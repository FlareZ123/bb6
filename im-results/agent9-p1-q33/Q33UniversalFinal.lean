import UniformUniversalCylinder
import Q33Finite

namespace BB6.Agent9Q33Universal

/-- Original-source demonstration of the universal fixed-base certificate
    extension, using precisely the previously certified q33 finite graphs. -/
theorem q33_universal_cylinder (r : Nat) :
    ¬ BB6.Agent1.Reach 2
       (14*2^(16*(33+2^(10+41)*r)+2) -
        2*(16*(33+2^(10+41)*r)+2)-10) := by
  exact BB6.Agent9UniformUniversal.universal_blank_critical_cylinder
    33 (by decide)
    BB6.Agent9Q33.q33L0Nodes BB6.Agent9Q33.q33L1Nodes
    BB6.Agent9Q33.q33L0_root BB6.Agent9Q33.q33L1_root
    BB6.Agent9Q33.q33L0_closed BB6.Agent9Q33.q33L1_closed
    BB6.Agent9Q33.q33L0_small BB6.Agent9Q33.q33L1_small
    BB6.Agent9Q33.q33L0_no1024 BB6.Agent9Q33.q33L1_no1024 r

#print axioms q33_universal_cylinder
end BB6.Agent9Q33Universal

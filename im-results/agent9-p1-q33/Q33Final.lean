import Q33Finite
import GenericCritical41K

namespace BB6.Agent9Q33

/-- The original P1 machine cannot visit the critical reset gate with exponent 530.
    This is one exact gate exclusion; the BB(6) machine remains undecided. -/
theorem blank_no_critical_530 :
    ¬ BB6.Agent1.Reach 2 (14*2^530-2*530-10) := by
  have h := BB6.Agent9Generic41K.critical_unreachable_of_shadow41K
      33 (by decide) q33L0Nodes q33L1Nodes
      q33L0_root q33L1_root
      q33L0_closed q33L1_closed
      q33L0_small q33L1_small
      q33L0_no1024 q33L1_no1024
  simpa only [show 16*33+2=530 by decide] using h

#print axioms blank_no_critical_530
end BB6.Agent9Q33

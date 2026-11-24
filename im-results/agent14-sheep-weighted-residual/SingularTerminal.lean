import SingularLowH
import ThreeAdicLTE
namespace SheepWeightedResidual

theorem type1_terminal_all (k H B : Nat) (hB : 1≤B)
    (heq : 3^H*(5+135*k)=2^H*(2^B-1)) : 32≤B := by
  by_cases h : H<3
  · exact type1_terminal_low k H B h heq
  · have ht := type1_terminal_H_ge_3_lower_bound k H B (by omega) hB heq
    omega

theorem type3_terminal_all (k H B : Nat) (hB : 1≤B)
    (heq : 3^H*(19+1683*k)=2^H*(2^B-1)) : 11502≤B := by
  by_cases h : H<9
  · exact type3_terminal_low k H B h heq
  · have ht := type3_terminal_H_ge_9_lower_bound k H B (by omega) hB heq
    omega

#print axioms type1_terminal_all
#print axioms type3_terminal_all
end SheepWeightedResidual

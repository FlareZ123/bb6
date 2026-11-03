import SourceBridge
import SecondMod96

namespace A4Backward

theorem source_no_second_gate_5_29 (j m k : Nat)
    (hj : j%96=5) (hm : m%96=29)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := A41.second_target_5_29_mod96 j m k hj hm heq
  exact source_no_cylinder_13_31 (2*j+3) k ha hk h

#print axioms source_no_second_gate_5_29
end A4Backward

import SourceBridge
import SecondMod96
set_option maxHeartbeats 0
namespace A4Backward

theorem second_target_A13_mod96 (j m k : Nat)
    (hj : j%48=5) (hm : (j+3*m)%96=92)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=13 ∧ k%96=31 := by
  have hm2 : 2≤m := by omega
  have hp := A41.pow_even_ge6_mod96 m hm2
  have hjp : (j+3)%48=8 := by omega
  have hr : (2^(2*m+2)*(j+3))%96=32 := by
    rw [Nat.mul_mod,hp]
    omega
  have hk : (k+j+3*m+5)%96=32 := by rw [heq]; exact hr
  omega

theorem second_target_A61_mod96 (j m k : Nat)
    (hj : j%48=29) (hm : (j+3*m)%96=44)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=61 ∧ k%96=79 := by
  have hm2 : 2≤m := by omega
  have hp := A41.pow_even_ge6_mod96 m hm2
  have hjp : (j+3)%48=32 := by omega
  have hr : (2^(2*m+2)*(j+3))%96=32 := by
    rw [Nat.mul_mod,hp]
    omega
  have hk : (k+j+3*m+5)%96=32 := by rw [heq]; exact hr
  omega

theorem source_no_second_gate_A13 (j m k : Nat)
    (hj : j%48=5) (hm : (j+3*m)%96=92)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_target_A13_mod96 j m k hj hm heq
  exact source_no_cylinder_13_31 (2*j+3) k ha hk h

theorem source_no_second_gate_A61 (j m k : Nat)
    (hj : j%48=29) (hm : (j+3*m)%96=44)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_target_A61_mod96 j m k hj hm heq
  exact source_no_cylinder_61_79 (2*j+3) k ha hk h

#print axioms second_target_A13_mod96
#print axioms second_target_A61_mod96
#print axioms source_no_second_gate_A13
#print axioms source_no_second_gate_A61
end A4Backward

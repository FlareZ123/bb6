import SourceBridgeB
import SecondMod96

set_option maxHeartbeats 0
namespace A4BackwardB

theorem second_target_B29_mod96 (j m k : Nat)
    (hj : j%48=13) (hm : (j+3*m)%96=76)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=29 ∧ k%96=79 := by
  have hm2 : 2≤m := by omega
  have hp := A41.pow_even_ge6_mod96 m hm2
  have hjp : (j+3)%48=16 := by omega
  have hr : (2^(2*m+2)*(j+3))%96=64 := by
    rw [Nat.mul_mod,hp]
    omega
  have hk : (k+j+3*m+5)%96=64 := by rw [heq]; exact hr
  omega

theorem second_target_B77_mod96 (j m k : Nat)
    (hj : j%48=37) (hm : (j+3*m)%96=28)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=77 ∧ k%96=31 := by
  have hm2 : 2≤m := by omega
  have hp := A41.pow_even_ge6_mod96 m hm2
  have hjp : (j+3)%48=40 := by omega
  have hr : (2^(2*m+2)*(j+3))%96=64 := by
    rw [Nat.mul_mod,hp]
    omega
  have hk : (k+j+3*m+5)%96=64 := by rw [heq]; exact hr
  omega

theorem source_no_second_gate_B29 (j m k : Nat)
    (hj : j%48=13) (hm : (j+3*m)%96=76)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_target_B29_mod96 j m k hj hm heq
  exact source_no_cylinder_29_79 (2*j+3) k ha hk h

theorem source_no_second_gate_B77 (j m k : Nat)
    (hj : j%48=37) (hm : (j+3*m)%96=28)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_target_B77_mod96 j m k hj hm heq
  exact source_no_cylinder_77_31 (2*j+3) k ha hk h

#print axioms second_target_B29_mod96
#print axioms second_target_B77_mod96
#print axioms source_no_second_gate_B29
#print axioms source_no_second_gate_B77
end A4BackwardB

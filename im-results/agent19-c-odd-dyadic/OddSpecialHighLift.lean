import OddSpecialLift
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent19Special

private theorem power128 (m : Nat) (hm:3≤m) :
    128 ∣ 2^(2*m+2) ∧ 256≤2^(2*m+2) := by
  have h7 : 7≤2*m+2 := by omega
  have h8 : 8≤2*m+2 := by omega
  constructor
  · change 2^7 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 h7
  · have hp := Nat.pow_le_pow_right (by decide : 0<2) h8
    simpa only [show (2:Nat)^8=256 by decide] using hp

/-- First lifted cylinder: x=13 mod16 and k=22 mod128. -/
theorem high_special_lift_a_coordinates (j m k : Nat)
    (hm : 3≤m) (hj : j%8=5)
    (hpair : (j+3*m+27)%128=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ u v, 1≤v ∧ 2*j+3=16*u+13 ∧ k=128*v+22 := by
  obtain ⟨hdiv,hB256⟩ := power128 m hm
  have hprodmod : 128 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%128=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hprodmod
  have hkmod : k%128=22 := by omega
  have hhlin := BB6.Agent46.pow_two_linear m
  have hpstep : 2^(2*m+3)=2*2^(2*m+2) := by
    rw [show 2*m+3=(2*m+2)+1 by omega,Nat.pow_succ]
    omega
  have hlin : 2*m+4≤2^(2*m+2) := by omega
  have hJ : 256*j≤2^(2*m+2)*j :=
    Nat.mul_le_mul_right j hB256
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hj5 : 5≤j := by omega
  have hkbig : 150≤k := by omega
  refine ⟨j/8,k/128,?_ ,?_ ,?_⟩ <;> omega

/-- Second lifted cylinder: x=5 mod16 and k=86 mod128. -/
theorem high_special_lift_b_coordinates (j m k : Nat)
    (hm : 3≤m) (hj : j%8=1)
    (hpair : (j+3*m+91)%128=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ u v, 2*j+3=16*u+5 ∧ k=128*v+86 := by
  obtain ⟨hdiv,_⟩ := power128 m hm
  have hprodmod : 128 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%128=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hprodmod
  have hkmod : k%128=86 := by omega
  refine ⟨j/8,k/128,?_ ,?_⟩ <;> omega

theorem blank_no_high_special_lift_a (j m k : Nat)
    (hm : 3≤m) (hj : j%8=5)
    (hpair : (j+3*m+27)%128=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,hv,ha,hk⟩ := high_special_lift_a_coordinates j m k hm hj hpair heq
  intro hr
  rw [ha,hk] at hr
  exact blank_no_special_lift_a u v hv hr

theorem blank_no_high_special_lift_b (j m k : Nat)
    (hm : 3≤m) (hj : j%8=1)
    (hpair : (j+3*m+91)%128=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,ha,hk⟩ := high_special_lift_b_coordinates j m k hm hj hpair heq
  intro hr
  rw [ha,hk] at hr
  exact blank_no_special_lift_b u v hr

#print axioms high_special_lift_a_coordinates
#print axioms high_special_lift_b_coordinates
#print axioms blank_no_high_special_lift_a
#print axioms blank_no_high_special_lift_b
end BB6.Agent19Special

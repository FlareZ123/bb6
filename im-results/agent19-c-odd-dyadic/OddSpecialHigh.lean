import OddSpecialCylinders
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent19Special

private theorem power64 (m : Nat) (hm : 2≤m) :
    64 ∣ 2^(2*m+2) ∧ 64≤2^(2*m+2) := by
  have h6 : 6≤2*m+2 := by omega
  constructor
  · change 2^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 h6
  · have h := Nat.pow_le_pow_right (by decide : 0<2) h6
    simpa only [show (2:Nat)^6=64 by decide] using h

/-- The first exact high-family arithmetic specialization at k=10 mod64. -/
theorem high_special_a_coordinates (j m k : Nat)
    (hm : 2≤m) (hj : j%8=7)
    (hpair : (j+3*m+15)%64=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ u v, 1≤v ∧ 2*j+3=16*u+1 ∧ k=64*v+10 := by
  obtain ⟨hdiv,hB64⟩ := power64 m hm
  have hprodmod : 64 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%64=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hprodmod
  have hkmod : k%64=10 := by omega
  have hlin : 2*m+4≤2^(2*m+2) := BB6.Agent46.pow_two_linear m
  have hJ : 64*j≤2^(2*m+2)*j :=
    Nat.mul_le_mul_right j hB64
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hj7 : 7≤j := by omega
  have hkbig : 74≤k := by omega
  refine ⟨(j+1)/8,k/64,?_ ,?_ ,?_⟩ <;> omega

/-- The second exact high-family arithmetic specialization at k=42 mod64. -/
theorem high_special_b_coordinates (j m k : Nat)
    (hm : 2≤m) (hj : j%8=3)
    (hpair : (j+3*m+47)%64=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ u v, 2*j+3=16*u+9 ∧ k=64*v+42 := by
  obtain ⟨hdiv,_⟩ := power64 m hm
  have hprodmod : 64 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%64=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hprodmod
  have hkmod : k%64=42 := by omega
  refine ⟨j/8,k/64,?_ ,?_⟩ <;> omega

/-- Every genuine high stopper in the first new congruence family is
    excluded from the entire original Machine C blank section orbit. -/
theorem blank_no_high_special_a (j m k : Nat)
    (hm : 2≤m) (hj : j%8=7)
    (hpair : (j+3*m+15)%64=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,hv,ha,hk⟩ := high_special_a_coordinates j m k hm hj hpair heq
  intro hr
  rw [ha,hk] at hr
  exact blank_no_special_a u v hv hr

/-- Every genuine high stopper in the second new congruence family is
    excluded from the entire original Machine C blank section orbit. -/
theorem blank_no_high_special_b (j m k : Nat)
    (hm : 2≤m) (hj : j%8=3)
    (hpair : (j+3*m+47)%64=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,ha,hk⟩ := high_special_b_coordinates j m k hm hj hpair heq
  intro hr
  rw [ha,hk] at hr
  exact blank_no_special_b u v hr

#print axioms high_special_a_coordinates
#print axioms high_special_b_coordinates
#print axioms blank_no_high_special_a
#print axioms blank_no_high_special_b
end BB6.Agent19Special

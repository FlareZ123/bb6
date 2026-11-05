import OddSevenReach
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven

/-- Arithmetic reduction of high family to the special depth-three
    sum-seven sector, with the true stopping equation kept unchanged. -/
theorem high_sumseven_coordinates (j m k:Nat)
    (hm:3≤m) (hj:j%16=15)
    (hpair:(j+3*m+51)%256=0)
    (heq:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃u v, 1≤v ∧ 2*j+3=32*u+1 ∧ k=256*v+46 := by
  have h8 : 8≤2*m+2 := by omega
  have hdiv : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 h8
  have hB256 : 256≤2^(2*m+2) := by
    have hp:=Nat.pow_le_pow_right (by decide : 0<2) h8
    simpa only [show (2:Nat)^8=256 by decide] using hp
  have hproddiv : 256 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%256=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hproddiv
  have hkmod : k%256=46 := by omega
  have hhlin := BB6.Agent46.pow_two_linear m
  have hpstep : 2^(2*m+3)=2*2^(2*m+2) := by
    rw [show 2*m+3=(2*m+2)+1 by omega,Nat.pow_succ]
    omega
  have hlin : 2*m+4≤2^(2*m+2) := by omega
  have hJ : 256*j≤2^(2*m+2)*j :=
    Nat.mul_le_mul_right j hB256
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hj15 : 15≤j := by omega
  have hkbig : 302≤k := by omega
  refine ⟨(j+1)/16,k/256,?_ ,?_ ,?_⟩ <;> omega

/-- All authentic high stopping targets satisfying these depth-three
    sum-seven congruences lie outside the blank-origin section. -/
theorem blank_no_high_sumseven (j m k:Nat)
    (hm:3≤m) (hj:j%16=15)
    (hpair:(j+3*m+51)%256=0)
    (heq:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,hv,ha,hk⟩ := high_sumseven_coordinates j m k hm hj hpair heq
  intro hr
  rw [ha,hk] at hr
  exact blank_no_sumseven_new u v hv hr

#print axioms high_sumseven_coordinates
#print axioms blank_no_high_sumseven
end BB6.Agent19Seven

import OddSevenFourLink
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Four

private theorem margin (q : Nat) :
    3*(q+10)+147 ≤ 3*2^(2*(q+10)+2) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have he : 2*(q+1+10)+2 = (2*(q+10)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Every high stopping target with this unbounded congruence gate is
    in an original-source, source-time-independent forbidden cylinder. -/
theorem high_four_link_coordinates (j m k : Nat)
    (hm : m%16=10) (hpair : (j+3*m+19)%64=0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃u v, 2≤v ∧ 2*j+3=32*u+1 ∧ k=64*v+14 := by
  have hm10 : 10≤m := by omega
  have hmar : 3*m+147 ≤ 3*2^(2*m+2) := by
    have hh:=margin (m-10)
    simpa only [show (m-10)+10=m by omega] using hh
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hpmul : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  have hkbig : 142≤k := by
    rw [hprod] at hstop
    omega
  have hpow : 64 ∣ 2^(2*m+2) := by
    change 2^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdiv : 64 ∣ 2^(2*m+2)*(j+3) := by
    obtain ⟨q,hq⟩ := hpow
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%64=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hkmod : k%64=14 := by omega
  have hamod : (2*j+3)%32=1 := by omega
  refine ⟨(2*j+3)/32,k/64,?_,?_,?_⟩ <;> omega

/-- Infinite true-blank high halting parameters eliminated by the
    four-link source-exact predecessor obstruction. -/
theorem blank_no_high_fourlink (j m k : Nat)
    (hm : m%16=10) (hpair : (j+3*m+19)%64=0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,hv,ha,hk⟩ := high_four_link_coordinates j m k hm hpair hstop
  intro hr
  rw [ha,hk] at hr
  exact blank_no_four_link_slope u v hv hr

#print axioms high_four_link_coordinates
#print axioms blank_no_high_fourlink
end BB6.Agent19Four

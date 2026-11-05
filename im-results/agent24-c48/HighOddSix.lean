import HighOddTwo
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

/-- A second high-family root-inaccessible cylinder, requiring three
    uniquely forced original source edges before the odd-right contradiction. -/
theorem blank_no_high_five_six32 (u v : Nat) (hv : 2≤v) :
    ¬ BB6.Agent3.CReach (8*u+5) (32*v+6) := by
  intro hr
  have h1 : BB6.Agent3.CReach (8*u+32*v+9) (16*v+2) := by
    have h := (six_even_right_blank_reach_iff
      (8*u+5) (32*v+6) (by omega) (by omega) (by omega) (by omega)).mp hr
    have hx : (8*u+5)+(32*v+6)-2=8*u+32*v+9 := by omega
    have hy : ((32*v+6)-2)/2=16*v+2 := by omega
    rw [hx,hy] at h
    exact h
  have h2 : BB6.Agent3.CReach (8*u+48*v+9) (8*v) := by
    have h := (six_even_right_blank_reach_iff
      (8*u+32*v+9) (16*v+2) (by omega) (by omega)
      (by omega) (by omega)).mp h1
    have hx : (8*u+32*v+9)+(16*v+2)-2=8*u+48*v+9 := by omega
    have hy : ((16*v+2)-2)/2=8*v := by omega
    rw [hx,hy] at h
    exact h
  have h3 : BB6.Agent3.CReach (8*u+56*v+7) (4*v-1) := by
    have h := (BB6.Agent15.blank_reach_iff_affine
      (8*u+48*v+9) (8*v) (by omega) (by omega) (by omega)).mp h2
    have hx : (8*u+48*v+9)+(8*v)-2=8*u+56*v+7 := by omega
    have hy : ((8*v)-2)/2=4*v-1 := by omega
    rw [hx,hy] at h
    exact h
  rcases h3 with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (8*u+56*v+7) (4*v-1) hn (by omega) (by omega)
      omega

/-- Source exact exclusion of a second higher stopping parameter cylinder. -/
theorem blank_no_high_halt_mod32pair (j m k : Nat)
    (hm : 2≤m) (hj : j%4=1)
    (hpair : (j+3*m+11)%32=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hj1 : 1≤j := by omega
  have hpower : 64 ∣ 2^(2*m+2) := by
    change 2^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowerpos : 0<2^(2*m+2) := Nat.pow_pos (by decide)
  obtain ⟨p,hp⟩ := hpower
  have hB64 : 64≤2^(2*m+2) := by omega
  have hlinear := pow_two_linear m
  have hpstep : 2^(2*m+3)=2*(2^(2*m+2)) := by
    rw [show 2*m+3=(2*m+2)+1 by omega,Nat.pow_succ]
    omega
  have hBlin : 2*m+4≤2^(2*m+2) := by omega
  have hJ : 64*j ≤ 2^(2*m+2)*j :=
    Nat.mul_le_mul_right j hB64
  have h3 : 3*(2*m+4) ≤ 3*2^(2*m+2) :=
    Nat.mul_le_mul_left 3 hBlin
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hkbig : 70≤k := by omega
  have hpow32 : 32 ∣ 2^(2*m+2) := by
    change 2^5 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hpow32
  have hdiv : 32 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨w*(j+3),?_⟩
    rw [hw]
    ac_rfl
  have hmod : (k+j+3*m+5)%32=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hkmod : k%32=6 := by omega
  have huform : 2*j+3=8*((j-1)/4)+5 := by omega
  have hvform : k=32*(k/32)+6 := by omega
  have hv : 2≤k/32 := by omega
  intro hr
  rw [huform,hvform] at hr
  exact blank_no_high_five_six32 ((j-1)/4) (k/32) hv hr

#print axioms blank_no_high_five_six32
#print axioms blank_no_high_halt_mod32pair
end BB6.Agent46

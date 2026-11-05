import SixResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

/-- Entire two-parameter original-blank forbidden cylinder with first
    coordinate congruent one mod8 and second congruent two mod16. Both
    inverse edges are uniquely forced into an odd-right image violation. -/
theorem blank_no_high_one_two16 (u v : Nat) (hu : 1≤u) (hv : 2≤v) :
    ¬ BB6.Agent3.CReach (8*u+1) (16*v+2) := by
  intro hr
  have hfirst : BB6.Agent3.CReach (8*u+16*v+1) (8*v) := by
    have hh := (six_even_right_blank_reach_iff
      (8*u+1) (16*v+2)
      (by omega) (by omega) (by omega) (by omega)).mp hr
    have hx : (8*u+1)+(16*v+2)-2=8*u+16*v+1 := by omega
    have hy : ((16*v+2)-2)/2=8*v := by omega
    rw [hx,hy] at hh
    exact hh
  have hsecond : BB6.Agent3.CReach (8*u+24*v-1) (4*v-1) := by
    have hh := (BB6.Agent15.blank_reach_iff_affine
      (8*u+16*v+1) (8*v) (by omega) (by omega) (by omega)).mp hfirst
    have hx : (8*u+16*v+1)+(8*v)-2=8*u+24*v-1 := by omega
    have hy : ((8*v)-2)/2=4*v-1 := by omega
    rw [hx,hy] at hh
    exact hh
  rcases hsecond with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (8*u+24*v-1) (4*v-1) hn (by omega) (by omega)
      omega

/-- All genuine original-source high-family halting candidates with this
    modular parameter equation fall into the forbidden cylinder above. -/
theorem blank_no_high_halt_mod16pair (j m k : Nat)
    (hm : 2≤m)
    (hj : j%4=3)
    (hpair : (j+3*m+7)%16=0)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hj3 : 3≤j := by omega
  have hpower : 16 ∣ 2^(2*m+2) := by
    change 2^4 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowerpos : 0<2^(2*m+2) := Nat.pow_pos (by decide)
  obtain ⟨p,hp⟩ := hpower
  have hB16 : 16≤2^(2*m+2) := by omega
  have hlinear := pow_two_linear m
  have hpstep : 2^(2*m+3)=2*(2^(2*m+2)) := by
    rw [show 2*m+3=(2*m+2)+1 by omega,Nat.pow_succ]
    omega
  have hBlin : 2*m+4≤2^(2*m+2) := by omega
  have hJ : 16*j ≤ 2^(2*m+2)*j :=
    Nat.mul_le_mul_right j hB16
  have h3 : 3*(2*m+4) ≤ 3*2^(2*m+2) :=
    Nat.mul_le_mul_left 3 hBlin
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hkbig : 34≤k := by omega
  have hprodmod : 16 ∣ 2^(2*m+2)*(j+3) := by
    exact dvd_mul_of_dvd_left hpower (j+3)
  have hmod : (k+j+3*m+5)%16=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hprodmod
  have hkmod : k%16=2 := by omega
  have hu : 1≤(j+1)/4 := by omega
  have huform : 2*j+3=8*((j+1)/4)+1 := by omega
  have hvform : k=16*(k/16)+2 := by omega
  have hv : 2≤k/16 := by omega
  intro hr
  rw [huform,hvform] at hr
  exact blank_no_high_one_two16 ((j+1)/4) (k/16) hu hv hr

#print axioms blank_no_high_one_two16
#print axioms blank_no_high_halt_mod16pair
end BB6.Agent46

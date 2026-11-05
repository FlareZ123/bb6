import MixedRectangle25Four
import MixedHighBoth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem rect_pow_bound (n : Nat) :
    3*(n+4)+41 ≤ 2^(2*(n+4)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+4)+2=(2*(n+4)+2)+2 := by omega
      rw [he, Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- A surviving infinite high stopping cylinder outside the previously
    integrated seven-low/five-high congruence exclusions. Every target
    enters the source-forbidden (x mod32=25,y mod32=4) rectangle. -/
theorem blank_no_high_rect_m4_j11 (j m k : Nat)
    (hm : m%32=4) (hj : j%32=11)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧ ¬ CReach (2*j+3) k := by
  have hm4 : 4≤m := by omega
  have hpow : 32 ∣ 2^(2*m+2) := by
    change 2^5 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨p,hp⟩ := hpow
  have hdiv : 32 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨p*(j+3),?_⟩
    rw [hp]
    ac_rfl
  have hmod : (k+j+3*m+5)%32=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hk32 : k%32=4 := by omega
  have hx32 : (2*j+3)%32=25 := by omega
  have hbig : 3*m+41≤2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃ q : Nat, m=q+4 := ⟨m-4,by omega⟩
    subst m
    exact rect_pow_bound q
  have hmul : j≤2^(2*m+2)*j := by
    have hp1 : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp1
  have hprod : 2^(2*m+2)*(j+3)=
      2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  have hk36 : 36≤k := by omega
  constructor
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    right
    exact ⟨j,m,rfl,hstop⟩
  · exact blank_no_rectangle_25_four (2*j+3) k hx32 hk32 hk36

#print axioms blank_no_high_rect_m4_j11
end BB6.Agent3

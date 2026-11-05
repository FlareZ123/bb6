import MixedRectangle27Zero
import MixedHighBoth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem rect_zero_pow_bound (n : Nat) :
    3*(n+5)+69 ≤ 2^(2*(n+5)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+5)+2=(2*(n+5)+2)+2 := by omega
      rw [he, Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- New infinitely many authentic high stopping inputs excluded from
    genuine blank reachability, including M512-abstractly admitted examples.
    Exact source rule, no simulation cutoff or conjectured orbit property. -/
theorem blank_no_high_rect_m5_j12 (j m k : Nat)
    (hm : m%32=5) (hj : j%32=12)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧ ¬ CReach (2*j+3) k := by
  have hm5 : 5≤m := by omega
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
  have hk32 : k%32=0 := by omega
  have hx32 : (2*j+3)%32=27 := by omega
  have hbig : 3*m+69≤2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃ q : Nat, m=q+5 := ⟨m-5,by omega⟩
    subst m
    exact rect_zero_pow_bound q
  have hmul : j≤2^(2*m+2)*j := by
    have hp1 : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp1
  have hprod : 2^(2*m+2)*(j+3)=
      2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  have hk64 : 64≤k := by omega
  constructor
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    right
    exact ⟨j,m,rfl,hstop⟩
  · exact blank_no_rectangle_27_zero (2*j+3) k hx32 hk32 hk64

#print axioms blank_no_high_rect_m5_j12
end BB6.Agent3

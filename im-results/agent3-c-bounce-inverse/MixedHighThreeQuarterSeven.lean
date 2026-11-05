import MixedEven4TwentyTwo
import MixedHighBoth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem even4_high_pow_bound (n : Nat) :
    3*(n+4)+69 ≤ 2^(2*(n+4)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+4)+2=(2*(n+4)+2)+2 := by omega
      rw [he,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- Broad three-quarters high-parameter sector, all unbounded m>=4 with
    m not 3 modulo4 and j=m+7 modulo32. Source stopping k is guaranteed
    to satisfy 2*x+k=22 modulo32 and the exact two-step inverse guards.
    This includes prior m=4,j=11 and m=5,j=12 modulo32 classes. -/
theorem blank_no_high_three_quarters_diff7 (j m k : Nat)
    (hm4 : 4≤m) (hm : m%4≠3)
    (hj : j%32=(m+7)%32)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧ ¬ CReach (2*j+3) k := by
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
  have hy4 : k%4=0 := by omega
  have h8 : k%16≠8 := by omega
  have h22 : (2*(2*j+3)+k)%32=22 := by omega
  have hbig : 3*m+69≤2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃ q : Nat, m=q+4 := ⟨m-4,by omega⟩
    subst m
    exact even4_high_pow_bound q
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
  · exact blank_no_even4_exeight_twenty_two
      (2*j+3) k hy4 h8 h22 hk64

#print axioms blank_no_high_three_quarters_diff7
end BB6.Agent3

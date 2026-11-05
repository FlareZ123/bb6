import MixedEven16TwentyTwo
import MixedHighBoth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem even16_high_pow_bound (n : Nat) :
    3*(n+5)+69 ≤ 2^(2*(n+5)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+5)+2=(2*(n+5)+2)+2 := by omega
      rw [he,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- A broad high-halting parameter cylinder with no finite parameter bound:
    m>=5, m=1 modulo4, and j=m+7 modulo32. Source-high stopping equation
    implies y divisible by 16 and 2*x+y=22 modulo 32, which is excluded
    by the fully original-source even16/22 two-step inverse theorem.
    It contains the previously separate m=5,j=12 modulo32 family. -/
theorem blank_no_high_one_mod4_diff7 (j m k : Nat)
    (hm5 : 5≤m) (hm : m%4=1)
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
  have hk16 : k%16=0 := by omega
  have h22 : (2*(2*j+3)+k)%32=22 := by omega
  have hbig : 3*m+69≤2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃ q : Nat, m=q+5 := ⟨m-5,by omega⟩
    subst m
    exact even16_high_pow_bound q
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
  · exact blank_no_even16_twenty_two (2*j+3) k hk16 h22 hk64

#print axioms blank_no_high_one_mod4_diff7
end BB6.Agent3

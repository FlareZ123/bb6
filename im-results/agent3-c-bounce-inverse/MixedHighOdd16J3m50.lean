import MixedOdd16DoubleForbidden
import MixedHighBoth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem odd16_high_pow_bound (n : Nat) :
    3*(n+5)+69 ≤ 2^(2*(n+5)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+5)+2=(2*(n+5)+2)+2 := by omega
      rw [he,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- Infinitely many genuine Machine C high stopping inputs are
    blank-unreachable by an exact TWO-PARENT high-valuation odd/odd
    source barrier. Unlike all prior single-predecessor source gates,
    this result requires disqualifying both full possible predecessor
    branches. No bounce recursion cutoff or computational time horizon. -/
theorem blank_no_high_odd16_j3m50 (j m k : Nat)
    (hm5 : 5≤m) (hm : m%4=1)
    (hj : j%64=(3*m+50)%64)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧ ¬ CReach (2*j+3) k := by
  have hpow : 64 ∣ 2^(2*m+2) := by
    change 2^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨p,hp⟩ := hpow
  have hdiv : 64 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨p*(j+3),?_⟩
    rw [hp]
    ac_rfl
  have hmod : (k+j+3*m+5)%64=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hx8 : (2*j+3)%8=5 := by omega
  have hk8 : k%8=3 := by omega
  have hsum64 : (2*j+3+k)%64=48 := by omega
  have hbig : 3*m+69≤2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃ q : Nat, m=q+5 := ⟨m-5,by omega⟩
    subst m
    exact odd16_high_pow_bound q
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
  · exact oddodd16_double_forbidden_rectangle
      (2*j+3) k hx8 hk8 hsum64 hk64

#print axioms blank_no_high_odd16_j3m50
end BB6.Agent3

import MixedEvenEightSharp
import MixedHighBoth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem high_eight_pow_bound (q : Nat) :
    3*(q+2)+32≤2^(2*(q+2)+2) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have he : 2*(q+1+2)+2=(2*(q+2)+2)+2 := by omega
      rw [he,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

/-- A broad third high Machine C stopping gate, previously omitted by
    the m0/1-mod4 two-step classes. All odd-j indices satisfying
    j+3m+5=0 mod8 with m≥2 reach an x1mod4,y0mod8 stopper.
    Their unique real source parent is an impossible odd image, yielding
    exact maximal incoming ancestry one from arbitrary roots. -/
theorem mixed_high_even_eight_sharp (j m k : Nat)
    (hm : 2≤m)
    (hj : j%2=1)
    (hres : (j+3*m+5)%8=0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+2) (some start) ≠
        some (2*j+3,k)) ∧
    (∃ start : Nat×Nat,
      BB6.Agent8Section.run secNext 1 (some start)=some (2*j+3,k)) ∧
    ¬ CReach (2*j+3) k := by
  have hbig : 3*m+32≤2^(2*m+2) := by
    obtain ⟨q,hq⟩ : ∃q:Nat,m=q+2 := ⟨m-2,by omega⟩
    subst m
    exact high_eight_pow_bound q
  have hmulp : j≤2^(2*m+2)*j := by
    have h1 : 1≤2^(2*m+2) := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j h1
  have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  have hk16 : 16≤k := by omega
  have hpow8 : 8 ∣ 2^(2*m+2) := by
    change 2^3 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdiv : 8 ∣ 2^(2*m+2)*(j+3) := by
    obtain ⟨v,hv⟩ := hpow8
    refine ⟨v*(j+3),?_⟩
    rw [hv]
    ac_rfl
  have hmod : (k+j+3*m+5)%8=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hk8 : k%8=0 := by omega
  have hx4 : (2*j+3)%4=1 := by omega
  have hsharp := mixed_even_eight_sharp (2*j+3) k hk16 hk8 hx4
  refine ⟨?_,hsharp.2.1,?_,hsharp.2.2⟩
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    right
    exact ⟨j,m,rfl,hstop⟩
  · refine ⟨((2*j+3)+k-2,(k-2)/2),?_⟩
    simpa [BB6.Agent8Section.run] using hsharp.1

#print axioms mixed_high_even_eight_sharp
end BB6.Agent3

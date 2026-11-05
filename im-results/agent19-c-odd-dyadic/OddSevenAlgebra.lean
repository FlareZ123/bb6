import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven

/-- Exact parity and 2-adic cost consequences of a recursive even bounce
    reaching the sum-7 target. -/
theorem source_bounce_target_algebra (u v a k n : Nat)
    (haodd : a%2=1) (hlt : a<2*k)
    (hsum : 32*u+256*v+48=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n =
      (32*u+1)+2*(256*v+46)+2) :
    n=1 ∧ a=8*u+64*v+9 ∧ k=12*u+224*v+37 := by
  have hnodd : n%2=1 := by omega
  have hres : (32*u+256*v+48)%32=16 := by omega
  by_cases hn3 : 3≤n
  · have hpow : 8 ∣ 2^n := by
      change 2^3 ∣ 2^n
      exact Nat.pow_dvd_pow 2 hn3
    obtain ⟨r,hr⟩ := hpow
    have hav : ∃q, a-1=2*q := ⟨(a-1)/2, by omega⟩
    obtain ⟨q,hq⟩ := hav
    have hfactor : 2*(a-1)+8=4*(q+2) := by omega
    have hdiv : 32 ∣ 32*u+256*v+48 := by
      refine ⟨r*(q+2),?_⟩
      calc
        32*u+256*v+48=2^n*(2*(a-1)+8) := hsum
        _=(8*r)*(4*(q+2)) := by rw [hr,hfactor]
        _=(8*4)*(r*(q+2)) := by ac_rfl
        _=32*(r*(q+2)) := by rfl
    have hzero : (32*u+256*v+48)%32=0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · have hn : n=1 := by omega
    subst n
    simp only [Nat.pow_one] at hsum
    constructor
    · rfl
    · constructor <;> omega

#print axioms source_bounce_target_algebra
end BB6.Agent19Seven

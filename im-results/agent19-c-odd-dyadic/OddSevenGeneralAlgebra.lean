import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven

/-- Original even-bounce input parity, output parity, output valuation
    and exact cost force exactly one recursive depth, for arbitrary target. -/
theorem general_source_bounce_depth_one (x y a k n : Nat)
    (hx : x%2=1) (hy : y%2=0) (ha : a%2=1) (hlt : a<2*k)
    (hmod : (x+y+1)%32=16)
    (hsum : x+y+1=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) :
    n=1 ∧ 4*a+12=x+y+1 ∧ 2*k+a+10=x+2*y := by
  have hnodd : n%2=1 := by omega
  by_cases hn3 : 3≤n
  · have hpow : 8 ∣ 2^n := by
      change 2^3 ∣ 2^n
      exact Nat.pow_dvd_pow 2 hn3
    obtain ⟨r,hr⟩ := hpow
    obtain ⟨q,hq⟩ : ∃q, a-1=2*q := ⟨(a-1)/2, by omega⟩
    have hfactor : 2*(a-1)+8=4*(q+2) := by omega
    have hdiv : 32 ∣ x+y+1 := by
      refine ⟨r*(q+2),?_⟩
      calc
        x+y+1=2^n*(2*(a-1)+8) := hsum
        _=(8*r)*(4*(q+2)) := by rw [hr,hfactor]
        _=(8*4)*(r*(q+2)) := by ac_rfl
        _=32*(r*(q+2)) := by rfl
    have hzero : (x+y+1)%32=0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · have hn : n=1 := by omega
    subst n
    simp only [Nat.pow_one] at hsum
    constructor
    · rfl
    · constructor <;> omega

#print axioms general_source_bounce_depth_one
end BB6.Agent19Seven

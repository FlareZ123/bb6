import Agent38SectionParity
import BounceHaltClosed
import Lean.Elab.Tactic.Omega

namespace BB6Agent38

open BB6.Agent46

/-- Exclude entire exponent/index congruence families in Agent 46's exact
    dyadic section halting basin, on the authentic blank orbit. -/
theorem dyadic_odd_depth_mod8_excluded (a k depth time : Nat)
    (ha : 3≤a) (hao : a%2=1) (hodd : depth%2=1)
    (hregion : a<2*k)
    (hlevel : 2*k-a+3=haltLevel (a-1) depth)
    (hcong : a%8=(3*depth)%8)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (a,k)) : False := by
  have hpow : 4 ∣ 2^(depth+1) := by
    change 2^2 ∣ 2^(depth+1)
    exact Nat.pow_dvd_pow 2 (by omega)
  have haeven : 2 ∣ a+3 := Nat.dvd_of_mod_eq_zero (by omega)
  have hdiv : 8 ∣ 2^(depth+1)*(a+3) := by
    rcases hpow with ⟨u,hu⟩
    rcases haeven with ⟨v,hv⟩
    refine ⟨u*v,?_⟩
    rw [hu,hv]
    calc
      4*u*(2*v) = (4*2)*(u*v) := by ac_rfl
      _ = 8*(u*v) := by rfl
  have hc := haltLevel_closed (a-1) depth
  have hsub : a-1+4=a+3 := by omega
  rw [hsub] at hc
  have hrelation : 2*k+a+3*depth+4=2^(depth+1)*(a+3) := by omega
  have hmod : (2*k+a+3*depth+4)%8=0 := by
    rw [hrelation]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hkodd : k%2=1 := by omega
  have hsum : (a+k)%4=2 := by omega
  have he := blank_section_mod4 time a k hr hkodd hsum
  have hfirst := (Prod.mk.inj he).1
  have hsecond := (Prod.mk.inj he).2
  omega

/-- Every one-left-counter dyadic halting input with depth 2 mod 8
    is excluded at all times from the actual blank section. -/
theorem dyadic_one_depth_two_mod8_excluded (k depth time : Nat)
    (hk : 4≤k)
    (hlevel : 2*k-3=haltLevel 4 depth)
    (hdepth : depth%8=2)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (1,k)) : False := by
  have hc := haltLevel_closed 4 depth
  have hrel : 2*k+3*depth+8=2^(depth+1)*8 := by omega
  have hdvd : 8 ∣ 2^(depth+1)*8 := by
    refine ⟨2^(depth+1),?_⟩
    omega
  have hmod : (2*k+3*depth+8)%8=0 := by
    rw [hrel]
    exact Nat.mod_eq_zero_of_dvd hdvd
  have hkodd : k%2=1 := by omega
  have hsum : (1+k)%4=2 := by omega
  have he := blank_section_mod4 time 1 k hr hkodd hsum
  have hx := (Prod.mk.inj he).1
  omega

#print axioms dyadic_one_depth_two_mod8_excluded

#print axioms dyadic_odd_depth_mod8_excluded
end BB6Agent38

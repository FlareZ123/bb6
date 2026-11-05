import MixedOdd16TwoInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem oddodd16_src_constructor (n a k x y : Nat)
    (ha2 : 2≤a) (haeven : a%2=0)
    (hk1 : 1≤k) (hregion : a<2*k)
    (hsum : x+y=2^n*(2*(a-1)+6))
    (hcost : (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y)
    (hy : 5≤y) : secNext (a,k)=some (x,y) := by
  have hc : sectionPreimageCriterion a k x y := by
    unfold sectionPreimageCriterion
    have hn0:a≠0 := by omega
    have hn1:a≠1 := by omega
    have hkn:k≠0 := by omega
    have hnot: ¬ 2*k≤a := by omega
    simp only [if_neg hn0,if_neg hn1,if_neg hkn,if_neg hnot,if_pos haeven]
    exact ⟨n,hsum,hcost⟩
  exact (complete_section_inverse a k x y hy).mpr hc

/-- Every large odd/odd source output with sum 16 modulo 32 has BOTH
    actual incoming edges. They correspond to depths 0 and 2 in the
    original source odd bounce recursion, without finite search. -/
theorem oddodd_sum16_two_parent_exist (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hsize : 64≤y)
    (hmod : (x+y)%32=16) :
    secNext ((x+y-4)/2,(x+3*y-10)/4)=some (x,y) ∧
    secNext ((x+y-16)/8,(7*x+15*y-88)/16)=some (x,y) := by
  let a0 := (x+y-4)/2
  let k0 := (x+3*y-10)/4
  let a2 := (x+y-16)/8
  let k2 := (7*x+15*y-88)/16
  have h0a : 2≤a0 ∧ a0%2=0 ∧ 1≤k0 ∧ a0<2*k0 := by
    dsimp [a0,k0]
    omega
  have h0sum : x+y=2^0*(2*(a0-1)+6) := by
    dsimp [a0]
    omega
  have h0cost : (2*k0-a0+3)+(2*(a0-1)+6)+3*0=x+2*y := by
    dsimp [a0,k0]
    omega
  have h2a : 2≤a2 ∧ a2%2=0 ∧ 1≤k2 ∧ a2<2*k2 := by
    dsimp [a2,k2]
    omega
  have h2sum : x+y=2^2*(2*(a2-1)+6) := by
    dsimp [a2]
    omega
  have h2cost : (2*k2-a2+3)+(2*(a2-1)+6)+3*2=x+2*y := by
    dsimp [a2,k2]
    omega
  exact ⟨oddodd16_src_constructor 0 a0 k0 x y h0a.1 h0a.2.1 h0a.2.2.1 h0a.2.2.2
    h0sum h0cost (by omega),
    oddodd16_src_constructor 2 a2 k2 x y h2a.1 h2a.2.1 h2a.2.2.1 h2a.2.2.2
    h2sum h2cost (by omega)⟩

#print axioms oddodd_sum16_two_parent_exist
end BB6.Agent3

import EvenOddAllDepthForbidden
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
namespace BB6.Agent13AllDepthFour

/-- A full original-source all-depth phase-four inverse path O then B.
    Its final blank-section state violates the certified odd-image
    condition; depth n=8*r+4 is unbounded. -/
theorem depth_four_OB_parent_impossible
    (u a k r q : Nat) (hq : 1≤q) (hk80 : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+4)=512*u+78)
    (hphase : (q+r)%8=4) :
    ¬ BB6.Agent3.CReach a k := by
  have hcostlin : k+4*q+12*r=256*u+31 := by omega
  have hao : a%2=1 := by omega
  have hko : k%2=1 := by omega
  have hsum4 : (a+k)%4=0 := by omega
  have hsum16 : (a+k)%16≠0 := by omega
  have hsize : 24≤a+k := by omega
  intro hr
  let x1 := (a+k-4)/2
  let y1 := (a+3*k-10)/4
  have hx1lin : x1+6*r=128*u+12+2*q := by
    dsimp [x1]
    omega
  have hy1lin : y1+q+9*r=192*u+20 := by
    dsimp [y1]
    omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      a k hao hko (by omega) hsum4 hsum16 hsize).mp hr
  have hy1 : 6≤y1 := by dsimp [y1]; omega
  have he1 : y1%2=0 := by omega
  have h10 : (x1+y1)%8≠0 := by omega
  have h17 : (x1+y1)%8≠7 := by omega
  let x2 := x1+y1-2
  let y2 := (y1-2)/2
  have hx2lin : x2+15*r=320*u+30+q := by
    dsimp [x2]
    omega
  have hy2lin : 2*y2+q+9*r=192*u+18 := by
    dsimp [y2]
    omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x1 y1 hy1 he1 h10 h17).mp h1
  have hy2 : 5≤y2 := by dsimp [y2]; omega
  have hyo2 : y2%2=1 := by omega
  have hsum2 : (x2+y2)%4=1 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x2 y2 hy2 hyo2 (Or.inl hsum2)) h2

/-- Independent all-depth phase-four O then F original-section inverse.
    Valid without a bound on the number of bounce cycles r. -/
theorem depth_four_OF_parent_impossible
    (u a k r q : Nat) (hq : 1≤q) (hk80 : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+4)=512*u+78)
    (hphase : (q+r)%16=3) :
    ¬ BB6.Agent3.CReach a k := by
  have hcostlin : k+4*q+12*r=256*u+31 := by omega
  have hao : a%2=1 := by omega
  have hko : k%2=1 := by omega
  have hsum4 : (a+k)%4=0 := by omega
  have hsum16 : (a+k)%16≠0 := by omega
  have hsize : 24≤a+k := by omega
  intro hr
  let x1 := (a+k-4)/2
  let y1 := (a+3*k-10)/4
  have hx1lin : x1+6*r=128*u+12+2*q := by
    dsimp [x1]
    omega
  have hy1lin : y1+q+9*r=192*u+20 := by
    dsimp [y1]
    omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      a k hao hko (by omega) hsum4 hsum16 hsize).mp hr
  have he1 : x1%2=0 := by omega
  have hyo1 : y1%2=1 := by omega
  have hy1 : 5≤y1 := by dsimp [y1]; omega
  have hfour : (x1+y1+1)%8=4 := by omega
  let x2 := (x1+y1-5)/2
  let y2 := (x1+3*y1-9)/4
  have hx2lin : 2*x2+15*r=320*u+27+q := by
    dsimp [x2]
    omega
  have hy2lin : 4*y2+q+33*r=704*u+63 := by
    dsimp [y2]
    omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent3.evenodd_four_blank_reach_iff
      x1 y1 he1 hyo1 hy1 hfour).mp h1
  have hy2 : 5≤y2 := by dsimp [y2]; omega
  have hyo2 : y2%2=1 := by omega
  have hsum2 : (x2+y2)%4=2 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x2 y2 hy2 hyo2 (Or.inr hsum2)) h2

#print axioms depth_four_OB_parent_impossible
#print axioms depth_four_OF_parent_impossible
end BB6.Agent13AllDepthFour

import EvenOddAllDepthPhaseFour
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
namespace BB6.Agent13AllDepthSix

/-- Additional original-source exclusion at every bounce depth 8r+6.
    The condition (q+7r)%8=0 forces the source-exact affine inverse A,
    followed by an odd/odd low-valuation inverse O, into the forbidden
    genuine blank-section odd image. It is disjoint from the existing
    (q+r)%2=1 depth-six family. -/
theorem depth_six_AO_parent_impossible
    (u a k r q : Nat) (hq : 1≤q) (hk80 : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+6)=512*u+78)
    (hphase : (q+7*r)%8=0) :
    ¬ BB6.Agent3.CReach a k := by
  have hcostlin : k+4*q+12*r=256*u+28 := by omega
  have hke : k%2=0 := by omega
  have hse : (a+k)%4=1 := by omega
  intro hr
  let x1 := a+k-2
  let y1 := (k-2)/2
  have hx1lin : x1+12*r=256*u+23+4*q := by
    dsimp [x1]
    omega
  have hy1lin : y1+2*q+6*r=128*u+13 := by
    dsimp [y1]
    omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent15.blank_reach_iff_affine
      a k (by omega) hke hse).mp hr
  have hxo : x1%2=1 := by omega
  have hyo : y1%2=1 := by omega
  have hy1 : 5≤y1 := by dsimp [y1]; omega
  have hs4 : (x1+y1)%4=0 := by omega
  have hs16 : (x1+y1)%16≠0 := by omega
  have hsize : 24≤x1+y1 := by omega
  let x2 := (x1+y1-4)/2
  let y2 := (x1+3*y1-10)/4
  have hx2lin : x2+9*r=192*u+16+q := by
    dsimp [x2]
    omega
  have hy2lin : 2*y2+q+15*r=320*u+26 := by
    dsimp [y2]
    omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      x1 y1 hxo hyo hy1 hs4 hs16 hsize).mp h1
  have hy2 : 5≤y2 := by dsimp [y2]; omega
  have hyo2 : y2%2=1 := by omega
  have hsum2 : (x2+y2)%4=1 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x2 y2 hy2 hyo2 (Or.inl hsum2)) h2

#print axioms depth_six_AO_parent_impossible
end BB6.Agent13AllDepthSix

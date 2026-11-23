import EvenOddAllDepthSieve
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13AllDepthShort

/-- All bounce depths 8r+6: an exact original-source A-O-B inverse word
    reaches the blank-forbidden odd image for one further q residue. -/
theorem depth_six_AOB_parent_impossible
    (u a k r q : Nat) (hq : 1 ≤ q) (hk : 80 ≤ k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+6)=512*u+78)
    (hphase : (q+15*r)%16=2) :
    ¬ BB6.Agent3.CReach a k := by
  have hcostlin : k+4*q+12*r=256*u+28 := by omega
  have hke : k%2=0 := by omega
  have hs : (a+k)%4=1 := by omega
  intro hr
  let x1 := a+k-2
  let y1 := (k-2)/2
  have hx1lin : x1+12*r=256*u+23+4*q := by
    dsimp [x1]; omega
  have hy1lin : y1+2*q+6*r=128*u+13 := by
    dsimp [y1]; omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent15.blank_reach_iff_affine
      a k (by omega) hke hs).mp hr
  have hxo1 : x1%2=1 := by omega
  have hyo1 : y1%2=1 := by omega
  have hy1 : 5 ≤ y1 := by dsimp [y1]; omega
  have hsum4 : (x1+y1)%4=0 := by omega
  have hsum16 : (x1+y1)%16≠0 := by omega
  have hsize : 24 ≤ x1+y1 := by omega
  let x2 := (x1+y1-4)/2
  let y2 := (x1+3*y1-10)/4
  have hx2lin : x2+9*r=192*u+16+q := by
    dsimp [x2]; omega
  have hy2lin : 2*y2+q+15*r=320*u+26 := by
    dsimp [y2]; omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      x1 y1 hxo1 hyo1 hy1 hsum4 hsum16 hsize).mp h1
  have hy2 : 6 ≤ y2 := by dsimp [y2]; omega
  have he2 : y2%2=0 := by omega
  have h20 : (x2+y2)%8≠0 := by omega
  have h27 : (x2+y2)%8≠7 := by omega
  let x3 := x2+y2-2
  let y3 := (y2-2)/2
  have hx3lin : x3+24*r=352*u+28+8*((q+15*r-2)/16) := by
    dsimp [x3]; omega
  have hy3lin : y3+4*((q+15*r-2)/16)=80*u+5 := by
    dsimp [y3]; omega
  have h3 : BB6.Agent3.CReach x3 y3 := by
    dsimp [x3,y3]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x2 y2 hy2 he2 h20 h27).mp h2
  have hy3 : 5 ≤ y3 := by dsimp [y3]; omega
  have hyo3 : y3%2=1 := by omega
  have hs3 : (x3+y3)%4=1 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x3 y3 hy3 hyo3 (Or.inl hs3)) h3

/-- All bounce depths 8r+6: the additional A-O-E source word uses the
    valuation-three even-left/odd-right inverse and ends in sum 2 mod4. -/
theorem depth_six_AOE_parent_impossible
    (u a k r q : Nat) (hq : 1 ≤ q) (hk : 80 ≤ k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+6)=512*u+78)
    (hphase : (q+31*r)%32=20) :
    ¬ BB6.Agent3.CReach a k := by
  have hcostlin : k+4*q+12*r=256*u+28 := by omega
  have hke : k%2=0 := by omega
  have hs : (a+k)%4=1 := by omega
  intro hr
  let x1 := a+k-2
  let y1 := (k-2)/2
  have hx1lin : x1+12*r=256*u+23+4*q := by
    dsimp [x1]; omega
  have hy1lin : y1+2*q+6*r=128*u+13 := by
    dsimp [y1]; omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent15.blank_reach_iff_affine
      a k (by omega) hke hs).mp hr
  have hxo1 : x1%2=1 := by omega
  have hyo1 : y1%2=1 := by omega
  have hy1 : 5 ≤ y1 := by dsimp [y1]; omega
  have hsum4 : (x1+y1)%4=0 := by omega
  have hsum16 : (x1+y1)%16≠0 := by omega
  have hsize : 24 ≤ x1+y1 := by omega
  let x2 := (x1+y1-4)/2
  let y2 := (x1+3*y1-10)/4
  have hx2lin : x2+9*r=192*u+16+q := by
    dsimp [x2]; omega
  have hy2lin : 2*y2+q+15*r=320*u+26 := by
    dsimp [y2]; omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      x1 y1 hxo1 hyo1 hy1 hsum4 hsum16 hsize).mp h1
  have he2 : x2%2=0 := by omega
  have hyo2 : y2%2=1 := by omega
  have hy2 : 5 ≤ y2 := by dsimp [y2]; omega
  have hs2 : (x2+y2+1)%16=8 := by omega
  have hsize2 : 23 ≤ x2+y2 := by omega
  let x3 := (x2+y2-5)/2
  let y3 := (x2+3*y2-9)/4
  have hx3lin : 2*x3+12*r=352*u+24+((q+15*r)/4) := by
    dsimp [x3]; omega
  have h3 : BB6.Agent3.CReach x3 y3 := by
    dsimp [x3,y3]
    exact (BB6.Agent3.odd_seven_blank_reach_iff
      x2 y2 he2 hyo2 hy2 hs2 hsize2).mp h2
  have hy3 : 5 ≤ y3 := by dsimp [y3]; omega
  have hyo3 : y3%2=1 := by omega
  have hs3 : (x3+y3)%4=2 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x3 y3 hy3 hyo3 (Or.inr hs3)) h3

/-- All bounce depths 8r+4: O-B-B-B is an additional exact original
    predecessor chain, independent of the previous O-B and O-F cells. -/
theorem depth_four_OBBB_parent_impossible
    (u a k r q : Nat) (hq : 1 ≤ q) (hk : 80 ≤ k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+4)=512*u+78)
    (hphase : (q+9*r)%32=14) :
    ¬ BB6.Agent3.CReach a k := by
  have hcostlin : k+4*q+12*r=256*u+31 := by omega
  have hao : a%2=1 := by omega
  have hko : k%2=1 := by omega
  have hsum4 : (a+k)%4=0 := by omega
  have hsum16 : (a+k)%16≠0 := by omega
  have hsize : 24 ≤ a+k := by omega
  intro hr
  let x1 := (a+k-4)/2
  let y1 := (a+3*k-10)/4
  have hx1lin : x1+6*r=128*u+12+2*q := by
    dsimp [x1]; omega
  have hy1lin : y1+q+9*r=192*u+20 := by
    dsimp [y1]; omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      a k hao hko (by omega) hsum4 hsum16 hsize).mp hr
  have hy1 : 6 ≤ y1 := by dsimp [y1]; omega
  have he1 : y1%2=0 := by omega
  have h10 : (x1+y1)%8≠0 := by omega
  have h17 : (x1+y1)%8≠7 := by omega
  let x2 := x1+y1-2
  let y2 := (y1-2)/2
  have hx2lin : x2+15*r=320*u+30+q := by
    dsimp [x2]; omega
  have hy2lin : 2*y2+q+9*r=192*u+18 := by
    dsimp [y2]; omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x1 y1 hy1 he1 h10 h17).mp h1
  have hy2 : 6 ≤ y2 := by dsimp [y2]; omega
  have he2 : y2%2=0 := by omega
  have h20 : (x2+y2)%8≠0 := by omega
  have h27 : (x2+y2)%8≠7 := by omega
  let x3 := x2+y2-2
  let y3 := (y2-2)/2
  have hx3lin : 2*x3+24*r=832*u+80+((q+9*r-14)/32)*32 := by
    dsimp [x3]; omega
  have h3 : BB6.Agent3.CReach x3 y3 := by
    dsimp [x3,y3]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x2 y2 hy2 he2 h20 h27).mp h2
  have hy3 : 6 ≤ y3 := by dsimp [y3]; omega
  have he3 : y3%2=0 := by omega
  have h30 : (x3+y3)%8≠0 := by omega
  have h37 : (x3+y3)%8≠7 := by omega
  let x4 := x3+y3-2
  let y4 := (y3-2)/2
  have h4 : BB6.Agent3.CReach x4 y4 := by
    dsimp [x4,y4]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x3 y3 hy3 he3 h30 h37).mp h3
  have hy4 : 5 ≤ y4 := by dsimp [y4]; omega
  have hyo4 : y4%2=1 := by omega
  have hs4 : (x4+y4)%4=1 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x4 y4 hy4 hyo4 (Or.inl hs4)) h4

#print axioms depth_six_AOB_parent_impossible
#print axioms depth_six_AOE_parent_impossible
#print axioms depth_four_OBBB_parent_impossible
end BB6.Agent13AllDepthShort

import EvenOddAllDepthForbidden
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent13AllDepthTwoDeep

/-- A second, disjoint arithmetic phase of arbitrarily high odd-bounce
    depth 8r+2 is blank-inaccessible, through the exact B-B-A-O
    predecessor word. The quotient+depth congruence q+19r=19 mod32
    uniformly exposes the forbidden original-machine odd image. -/
theorem depth_two_BBAO_source_parent_impossible
    (u a k r q : Nat) (hq : 1≤q) (hk80 : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+2)=512*u+78)
    (hphase : (q+19*r)%32=19) :
    ¬ BB6.Agent3.CReach a k := by
  let h := (q+3*r-3)/8
  have hmod8 : (q+3*r)%8=3 := by omega
  have hindex : q+3*r=8*h+3 := by
    have hh := Nat.mod_add_div (q+3*r) 8
    dsimp [h]
    omega
  have hhphase : (h+2*r)%4=2 := by omega
  have hcostlin : k+4*q+12*r=256*u+34 := by omega
  have hy0 : 6≤k := by omega
  have he0 : k%2=0 := by omega
  have h00 : (a+k)%8≠0 := by omega
  have h07 : (a+k)%8≠7 := by omega
  intro hr
  let x1 := a+k-2
  let y1 := (k-2)/2
  have hx1lin : x1+12*r=256*u+29+4*q := by
    dsimp [x1]
    omega
  have hy1lin : y1+2*q+6*r=128*u+16 := by
    dsimp [y1]
    omega
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      a k hy0 he0 h00 h07).mp hr
  have hy1 : 6≤y1 := by dsimp [y1]; omega
  have he1 : y1%2=0 := by omega
  have h10 : (x1+y1)%8≠0 := by omega
  have h17 : (x1+y1)%8≠7 := by omega
  let x2 := x1+y1-2
  let y2 := (y1-2)/2
  have hx2lin : x2+18*r=384*u+43+2*q := by
    dsimp [x2]
    omega
  have hy2lin : y2+q+3*r=64*u+7 := by
    dsimp [y2]
    omega
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x1 y1 hy1 he1 h10 h17).mp h1
  have hy2 : 4≤y2 := by dsimp [y2]; omega
  have he2 : y2%2=0 := by omega
  have hse2 : (x2+y2)%4=1 := by omega
  let x3 := x2+y2-2
  let y3 := (y2-2)/2
  have hx3lin : x3+21*r=448*u+48+q := by
    dsimp [x3]
    omega
  have hy3lin : 2*y3+q+3*r=64*u+5 := by
    dsimp [y3]
    omega
  have h3 : BB6.Agent3.CReach x3 y3 := by
    dsimp [x3,y3]
    exact (BB6.Agent15.blank_reach_iff_affine
      x2 y2 hy2 he2 hse2).mp h2

  have hx3h : x3+24*r=448*u+51+8*h := by omega
  have hy3h : y3+4*h=32*u+1 := by omega
  have hy3 : 5≤y3 := by dsimp [y3]; omega
  have hxo3 : x3%2=1 := by omega
  have hyo3 : y3%2=1 := by omega
  have hsum3 : (x3+y3)%4=0 := by omega
  have hsum16 : (x3+y3)%16≠0 := by omega
  have hsize3 : 24≤x3+y3 := by omega
  let x4 := (x3+y3-4)/2
  let y4 := (x3+3*y3-10)/4
  have hx4h : x4+12*r=240*u+24+2*h := by
    dsimp [x4]
    omega
  have hy4h : y4+h+6*r=136*u+11 := by
    dsimp [y4]
    omega
  have h4 : BB6.Agent3.CReach x4 y4 := by
    dsimp [x4,y4]
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      x3 y3 hxo3 hyo3 hy3 hsum3 hsum16 hsize3).mp h3
  have hy4 : 5≤y4 := by dsimp [y4]; omega
  have hyo4 : y4%2=1 := by omega
  have hsum4 : (x4+y4)%4=1 := by omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x4 y4 hy4 hyo4 (Or.inl hsum4)) h4

#print axioms depth_two_BBAO_source_parent_impossible
end BB6.Agent13AllDepthTwoDeep

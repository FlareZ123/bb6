import EvenOddTwoParentRoot
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13AllDepth

/-- Arbitrarily large even/odd original-source predecessor depths divisible
    by eight have an image forbidden by the authentic blank-section
    odd-right invariant, provided the target mass has two additional
    factors of two beyond that parent depth. This is an all-depth
    elimination, not a bounded enumeration of bounce counts. -/
theorem depth_eight_high_valuation_parent_unreachable
    (u a k r q : Nat) (hq : 1≤q) (hk5 : 5≤k)
    (hmass : 346*u+54=2^(8*r+4)*q)
    (hparent : 346*u+54=2^(8*r+1)*(a+3))
    (hcost : 2*k+a+7+3*(8*r)=512*u+78) :
    ¬ BB6.Agent3.CReach a k := by
  have hfactor : (2:Nat)^(8*r+4)=2^(8*r+1)*8 := by
    rw [show 8*r+4=(8*r+1)+3 by omega,Nat.pow_add]
    -- the power-of-two numeral simplifies by reflexivity
  have hnew : 346*u+54=(2:Nat)^(8*r+1)*(8*q) := by
    rw [hfactor] at hmass
    calc
      346*u+54=(2:Nat)^(8*r+1)*8*q := hmass
      _=(2:Nat)^(8*r+1)*(8*q) := by ac_rfl
  have he : (2:Nat)^(8*r+1)*(a+3)=
      (2:Nat)^(8*r+1)*(8*q) :=
    hparent.symm.trans hnew
  have hpos : 0<(2:Nat)^(8*r+1) :=
    Nat.pow_pos (by decide)
  have ha : a+3=8*q := Nat.eq_of_mul_eq_mul_left hpos he
  have hyo : k%2=1 := by omega
  have hs : (a+k)%4=2 := by omega
  exact BB6.Agent13TwoParent.odd_forbidden_image a k hk5 hyo
    (Or.inr hs)

/-- The congruence theorem also holds when the arithmetic source
    predecessor itself, rather than its target mass, is supplied.
    This variant is convenient in a complete inverse fan. -/
theorem depth_eight_odd_source_explicit_impossible
    (u a k r q : Nat) (hq : 1≤q) (hk5 : 5≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r)=512*u+78) :
    ¬ BB6.Agent3.CReach a k := by
  have hyo : k%2=1 := by omega
  have hs : (a+k)%4=2 := by omega
  exact BB6.Agent13TwoParent.odd_forbidden_image a k hk5 hyo
    (Or.inr hs)


/-- If the original odd-source bounce depth is 8r+6, the highest
    extracted dyadic factor produces an affine even-right parent. A
    single exact original-section inverse A then enters the forbidden
    blank odd-right image whenever q+r is odd. -/
theorem depth_six_parity_source_parent_impossible
    (u a k r q : Nat) (hk12 : 12≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+6)=512*u+78)
    (hpar : (q+r)%2=1) :
    ¬ BB6.Agent3.CReach a k := by
  have hke : k%2=0 := by omega
  have hse : (a+k)%4=1 := by omega
  have hyo : ((k-2)/2)%2=1 := by omega
  have hsum : ((a+k-2)+((k-2)/2))%4=2 := by omega
  intro hr
  have hsrc : BB6.Agent3.CReach (a+k-2) ((k-2)/2) :=
    (BB6.Agent15.blank_reach_iff_affine a k
      (by omega) hke hse).mp hr
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    (a+k-2) ((k-2)/2) (by omega) hyo (Or.inr hsum)) hsrc

/-- All-depth extension: the source-exact predecessor of depth 8r+6
    is blank-inaccessible whenever its target mass has valuation at
    least 8r+10 and the remaining quotient obeys q+r odd. -/
theorem depth_six_high_valuation_parent_unreachable
    (u a k r q : Nat) (hk12 : 12≤k)
    (hmass : 346*u+54=2^(8*r+10)*q)
    (hparent : 346*u+54=2^(8*r+7)*(a+3))
    (hcost : 2*k+a+7+3*(8*r+6)=512*u+78)
    (hpar : (q+r)%2=1) :
    ¬ BB6.Agent3.CReach a k := by
  have hfactor : (2:Nat)^(8*r+10)=2^(8*r+7)*8 := by
    rw [show 8*r+10=(8*r+7)+3 by omega,Nat.pow_add]
  have hnew : 346*u+54=(2:Nat)^(8*r+7)*(8*q) := by
    rw [hfactor] at hmass
    calc
      346*u+54=(2:Nat)^(8*r+7)*8*q := hmass
      _=(2:Nat)^(8*r+7)*(8*q) := by ac_rfl
  have he : (2:Nat)^(8*r+7)*(a+3)=
      (2:Nat)^(8*r+7)*(8*q) :=
    hparent.symm.trans hnew
  have hpos : 0<(2:Nat)^(8*r+7) :=
    Nat.pow_pos (by decide)
  have ha : a+3=8*q := Nat.eq_of_mul_eq_mul_left hpos he
  exact depth_six_parity_source_parent_impossible
    u a k r q hk12 ha hcost hpar


/-- A third arbitrarily deep original-section obstruction. At depth
    n=8r+2, one combined mod-eight condition forces two exact even-right
    inverse steps B,B and then one exact affine inverse A. The final
    odd-right image has coordinate sum 2 (mod 4), hence cannot belong
    to the actual blank orbit. No bound on r is imposed. -/
theorem depth_two_BBA_source_parent_impossible
    (u a k r q : Nat) (hk80 : 80≤k)
    (ha : a+3=8*q)
    (hcost : 2*k+a+7+3*(8*r+2)=512*u+78)
    (hphase : (q+3*r)%8=7) :
    ¬ BB6.Agent3.CReach a k := by
  have hy0 : 6≤k := by omega
  have he0 : k%2=0 := by omega
  have h00 : (a+k)%8≠0 := by omega
  have h07 : (a+k)%8≠7 := by omega
  intro hr
  let x1 := a+k-2
  let y1 := (k-2)/2
  have h1 : BB6.Agent3.CReach x1 y1 := by
    dsimp [x1,y1]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      a k hy0 he0 h00 h07).mp hr
  have hy1 : 6≤y1 := by dsimp [y1]; omega
  have he1 : y1%2=0 := by dsimp [x1,y1]; omega
  have h10 : (x1+y1)%8≠0 := by dsimp [x1,y1]; omega
  have h17 : (x1+y1)%8≠7 := by dsimp [x1,y1]; omega
  let x2 := x1+y1-2
  let y2 := (y1-2)/2
  have h2 : BB6.Agent3.CReach x2 y2 := by
    dsimp [x2,y2]
    exact (BB6.Agent46.six_even_right_blank_reach_iff
      x1 y1 hy1 he1 h10 h17).mp h1
  have hy2 : 4≤y2 := by dsimp [y2,x1,y1]; omega
  have he2 : y2%2=0 := by dsimp [y2,x1,y1]; omega
  have hse2 : (x2+y2)%4=1 := by
    dsimp [x2,y2,x1,y1]
    omega
  let x3 := x2+y2-2
  let y3 := (y2-2)/2
  have h3 : BB6.Agent3.CReach x3 y3 := by
    dsimp [x3,y3]
    exact (BB6.Agent15.blank_reach_iff_affine
      x2 y2 hy2 he2 hse2).mp h2
  have hy3 : 5≤y3 := by dsimp [y3,y2,y1,x2,x1]; omega
  have hyo3 : y3%2=1 := by
    dsimp [y3,y2,y1,x2,x1]
    omega
  have hs3 : (x3+y3)%4=2 := by
    dsimp [x3,y3,y2,y1,x2,x1]
    omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    x3 y3 hy3 hyo3 (Or.inr hs3)) h3

#print axioms depth_eight_high_valuation_parent_unreachable
#print axioms depth_eight_odd_source_explicit_impossible
#print axioms depth_six_parity_source_parent_impossible
#print axioms depth_six_high_valuation_parent_unreachable
#print axioms depth_two_BBA_source_parent_impossible
end BB6.Agent13AllDepth

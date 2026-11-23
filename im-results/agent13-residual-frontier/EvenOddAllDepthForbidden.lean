import EvenOddTwoParentRoot
import Lean.Elab.Tactic.Omega

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

#print axioms depth_eight_high_valuation_parent_unreachable
#print axioms depth_eight_odd_source_explicit_impossible
#print axioms depth_six_parity_source_parent_impossible
#print axioms depth_six_high_valuation_parent_unreachable
end BB6.Agent13AllDepth

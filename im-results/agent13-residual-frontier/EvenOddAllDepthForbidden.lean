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

#print axioms depth_eight_high_valuation_parent_unreachable
#print axioms depth_eight_odd_source_explicit_impossible
end BB6.Agent13AllDepth

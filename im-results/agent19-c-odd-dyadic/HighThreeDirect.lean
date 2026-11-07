import HighThreeDirectArithmetic
import DyadicThreeCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11HighThreeDirect

/-- A second, disjoint source-exact high stopping cylinder: here the
    authentic stopping target itself belongs to the newly proved odd-part
    three inverse cone. Every inverse depth r is permitted. -/
theorem high_three_direct_no_blank (r j m k : Nat)
    (hr : 2≤r) (hm : 3≤m) (hdepth : r+2≤2*m+2)
    (hm4 : m%4=(2*r+1)%4)
    (hpair : (j+3*m+3)%2^(r+2)=2^r)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,hu,hu4,hb,hmass⟩ :=
    high_three_direct_arithmetic r j m k hr hm hdepth hm4 hpair hstop
  exact BB6.Agent19ThreeCone.dyadic_three_cone_no_blank
    r (2*j+3) k u hu hu4 hb hmass

/-- Exact source high stopping target, without subtraction truncation. -/
theorem high_three_direct_stopping_target (r j m : Nat)
    (hr : 2≤r) (hm : 3≤m) (hdepth : r+2≤2*m+2)
    (hm4 : m%4=(2*r+1)%4)
    (hpair : (j+3*m+3)%2^(r+2)=2^r) :
    ¬ BB6.Agent3.CReach (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5)) := by
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hbound : j+3*m+5≤2^(2*m+2)*(j+3) := by
    have hp := pow_bound m (by omega)
    have hp1 : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
    have hj : j≤2^(2*m+2)*j := by
      simpa using Nat.mul_le_mul_right j hp1
    have hmarg : 3*m+5≤3*2^(2*m+2) := by omega
    rw [Nat.mul_add]
    omega
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hh := Nat.sub_add_cancel hbound
    omega
  exact high_three_direct_no_blank r j m k hr hm hdepth hm4 hpair hstop

#print axioms high_three_direct_no_blank
#print axioms high_three_direct_stopping_target
end BB6.Agent11HighThreeDirect

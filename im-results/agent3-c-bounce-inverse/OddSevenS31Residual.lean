import M0EvenEvenSumZero
import OddSevenSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3OddSevenResidual
open BB6.Agent11M0SumZero

/-- The residual E4 state in Agent 11's u=64*c+7 branch has a unique
    predecessor on the c=4*d+3 subfamily. -/
theorem u7_E4_parent (d : Nat)
    (hr : BB6.Agent3.CReach
      (186982898+239975840*d) (11087493+14229808*d)) :
    BB6.Agent3.CReach
      (99035193+127102824*d) (55061342+70666316*d) := by
  have hp := cReach_parent_of_left_gt5
    (186982898+239975840*d) (11087493+14229808*d)
    (by omega) hr
  rcases hp with ⟨a,k,hreach,hedge⟩
  have heq := (BB6.Agent3.odd_seven_parent_iff
    a k (186982898+239975840*d) (11087493+14229808*d)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp hedge
  have ha : a=99035193+127102824*d := by omega
  have hk : k=55061342+70666316*d := by omega
  simpa only [ha,hk] using hreach


private theorem e4_y_parent (e : Nat) :
    11087493+14229808*(4*e+3)=53776917+56919232*e := by omega

private theorem p0_x_parent (e : Nat) :
    99035193+127102824*(4*e+3)=480343665+508411296*e := by omega

private theorem p0_y_parent (e : Nat) :
    55061342+70666316*(4*e+3)=267060290+282665264*e := by omega

/-- On c=16*e+15, the forced odd/even parent itself is impossible:
    two six-even-right inverse steps reach an odd-right sum-two state. -/
theorem u7_E4_unreachable (e : Nat) :
    ¬ BB6.Agent3.CReach
      (906910418+959903360*e) (53776917+56919232*e) := by
  intro hr
  have hx0 : 186982898+239975840*(4*e+3)=906910418+959903360*e := by omega
  have hy0 := e4_y_parent e
  have hr0 : BB6.Agent3.CReach
      (186982898+239975840*(4*e+3)) (11087493+14229808*(4*e+3)) := by
    simpa only [hx0,hy0] using hr
  have hp0 := u7_E4_parent (4*e+3) hr0
  have hxP0 := p0_x_parent e
  have hyP0 := p0_y_parent e
  have hp0' : BB6.Agent3.CReach
      (480343665+508411296*e) (267060290+282665264*e) := by
    simpa only [hxP0,hyP0] using hp0
  have hp1 := (BB6.Agent46.six_even_right_blank_reach_iff
    (480343665+508411296*e) (267060290+282665264*e)
    (by omega) (by omega) (by omega) (by omega)).mp hp0'
  have hp1' : BB6.Agent3.CReach
      (747403953+791076560*e) (133530144+141332632*e) := by
    have hx : (480343665+508411296*e)+(267060290+282665264*e)-2 =
        747403953+791076560*e := by omega
    have hy : ((267060290+282665264*e)-2)/2 =
        133530144+141332632*e := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (BB6.Agent46.six_even_right_blank_reach_iff
    (747403953+791076560*e) (133530144+141332632*e)
    (by omega) (by omega) (by omega) (by omega)).mp hp1'
  have hp2' : BB6.Agent3.CReach
      (880934095+932409192*e) (66765071+70666316*e) := by
    have hx : (747403953+791076560*e)+(133530144+141332632*e)-2 =
        880934095+932409192*e := by omega
    have hy : ((133530144+141332632*e)-2)/2 =
        66765071+70666316*e := by omega
    simpa only [hx,hy] using hp2
  exact (BB6.Agent11High.blank_no_odd_sum_two
    (880934095+932409192*e) (66765071+70666316*e)
    (by omega) (by omega) (by omega)) hp2'

#print axioms u7_E4_unreachable

#print axioms u7_E4_parent
end BB6.Agent3OddSevenResidual

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

#print axioms u7_E4_parent
end BB6.Agent3OddSevenResidual

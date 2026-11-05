import NeedleTerminalAffineSource
import NeedleTripleDistinctSource
import NeedleThreeTerminalParents
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleTriple
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open NeedlePeriodTriple

/-- Infinite terminal powers with three distinct legal synthetic predecessors. -/
theorem authentic_three_terminal_sources (t : Nat) :
    ∃ d0 d3 d20 : Nat,
      d0≠d3 ∧ d0≠d20 ∧ d3≠d20 ∧
      highLevelNext (.N d0)=some (.N (2^(exponent t)-2)) ∧
      highLevelNext (.N d3)=some (.N (2^(exponent t)-2)) ∧
      highLevelNext (.N d20)=some (.N (2^(exponent t)-2)) := by
  obtain ⟨q0,q3,q20,hq0,hq3,hq20,_,_,_⟩ :=
    NeedleThreeTerminalParents.three_terminal_parents t
  have hK : 1≤exponent t := by simp [exponent]; omega
  have he0 : NeedleInverse.den 0*q0+NeedleInverse.bias 0=
      (2:Nat)^(exponent t) := by
    change 5*q0+6=(2:Nat)^(exponent t)
    exact hq0
  have he3 : NeedleInverse.den 3*q3+NeedleInverse.bias 3=
      (2:Nat)^(exponent t) := by
    change 19*q3+30=(2:Nat)^(exponent t)
    exact hq3
  have he20 : NeedleInverse.den 20*q20+NeedleInverse.bias 20=
      (2:Nat)^(exponent t) := by
    change 2097155*q20+3145751=(2:Nat)^(exponent t)
    exact hq20
  obtain ⟨hd03,hd020,hd320⟩ := distinct_three_oddTowers q0 q3 q20
  exact ⟨oddTower q0 0,oddTower q3 3,oddTower q20 20,
    hd03,hd020,hd320,
    authentic_affine_successor q0 0 (exponent t) hK he0,
    authentic_affine_successor q3 3 (exponent t) hK he3,
    authentic_affine_successor q20 20 (exponent t) hK he20⟩

#print axioms authentic_three_terminal_sources
end BB6.Agent20.SpaceNeedleTriple

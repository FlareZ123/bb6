import Q0151B2AbstractActions
import Q0151ParamSaturation

set_option maxHeartbeats 0

/-!
Complete all-length B2/second-length-4k+5 finite pop-action
refinement. The genuine source physically transfers the current
segment followed by 1110 (10)^(2k+1) 1 and pops the saved physical
segment. The finite model admits j=1 for every second-run category 5;
parametric saturation proves that its shortened suffix has exactly
the same right-summary request for any k≥0.
-/

namespace BB6.Agent5Q0151B2OddActionSound
open BB6.Agent5Q0151B2AbstractActions
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151ParamSaturation

theorem b2_odd_action (s : SegmentSummary)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP)
    (n : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::(4*n+4)::rest)) ≠ 0) :
    Action.pop (segConcat
      (segAppend s
        ([true,true,true,false] ++ altWord (2*n+1) ++ [true]))
      (rightSig rest)) ∈
      delta (mkControl true (rightSig (1::(4*n+4)::rest)) s) := by
  have hh := second_five_action s n rest h
  have hs := two_zero_repair_positive s (n+1) (by omega)
    [true] hN hP
  have hlen : 2*(n+1)-1=2*n+1 := by omega
  rw [hlen] at hs
  rw [hs]
  exact hh

#print axioms b2_odd_action
end BB6.Agent5Q0151B2OddActionSound

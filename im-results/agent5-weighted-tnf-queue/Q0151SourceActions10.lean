import Q0151SourceActions8
import Q0151OuterAbstractActions
import Q0151ParamSaturation

set_option maxHeartbeats 0

/-!
Original six-state Turing-machine B/C macro transition refinement for
ALL run lengths 4k+4 and 4k+5, all k≥0, all physical left segments and
arbitrary marker stacks. Each joint conclusion supplies BOTH a
positive-length primitive-source execution and an exact action in
the finite 814-control interpreter; thus it closes four unbounded
nonexceptional source cases without numerical run-length cutoffs.
-/

namespace BB6.Agent5Q0151SourceActions10
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151ParamSaturation
open BB6.Agent5Q0151OuterAbstractActions
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions8

theorem b_four_refines (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig ((4*n+3)::rest)) ≠ 0) :
    Action.push
      (co false (alt (2*n) ++ [true,true,true]) rest)
      (segAppend emptySegment s) ∈
        delta (co true s ((4*n+3)::rest)) ∧
    Goes (boundary 1 s stack (runBits ((4*n+3)::rest)))
      (boundary 2 (alt (2*n) ++ [true,true,true])
        (s::stack) (runBits rest)) := by
  have ha := b_four_push (segAppend emptySegment s) n rest hlive
  constructor
  · simpa [co,alt_eq_altWord] using ha
  · simpa [runBits] using b_zero n s stack (runBits rest)

theorem c_four_refines (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig ((4*n+3)::rest)) ≠ 0) :
    Action.stay
      (co false (s ++ alt (2*n+1) ++ [true,true,true]) rest) ∈
        delta (co false s ((4*n+3)::rest)) ∧
    Goes (boundary 2 s stack (runBits ((4*n+3)::rest)))
      (boundary 2 (s ++ alt (2*n+1) ++ [true,true,true])
        stack (runBits rest)) := by
  have hlow := segAppend_lower emptySegment
    (by decide) (by decide) s
  have ha := c_four_stay (segAppend emptySegment s)
    hlow.1 hlow.2 n rest hlive
  constructor
  · simpa [co,segAppend_append,alt_eq_altWord,List.append_assoc]
      using ha
  · simpa [runBits] using c_zero n s stack (runBits rest)

theorem b_five_refines (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig ((4*n+4)::rest)) ≠ 0) :
    Action.push
      (co true (alt (2*n+1) ++ [true,true]) rest)
      (segAppend emptySegment s) ∈
        delta (co true s ((4*n+4)::rest)) ∧
    Goes (boundary 1 s stack (runBits ((4*n+4)::rest)))
      (boundary 1 (alt (2*n+1) ++ [true,true])
        (s::stack) (runBits rest)) := by
  have ha := b_five_push (segAppend emptySegment s) n rest hlive
  constructor
  · simpa [co,alt_eq_altWord] using ha
  · simpa [runBits] using b_big_one n s stack (runBits rest)

theorem c_five_refines (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig ((4*n+4)::rest)) ≠ 0) :
    Action.stay
      (co true (s ++ alt (2*n+2) ++ [true,true]) rest) ∈
        delta (co false s ((4*n+4)::rest)) ∧
    Goes (boundary 2 s stack (runBits ((4*n+4)::rest)))
      (boundary 1 (s ++ alt (2*n+2) ++ [true,true])
        stack (runBits rest)) := by
  have hlow := segAppend_lower emptySegment
    (by decide) (by decide) s
  have ha := c_five_stay (segAppend emptySegment s)
    hlow.1 hlow.2 n rest hlive
  constructor
  · simpa [co,segAppend_append,alt_eq_altWord,List.append_assoc]
      using ha
  · simpa [runBits] using c_big_one n s stack (runBits rest)

#print axioms b_four_refines
#print axioms c_four_refines
#print axioms b_five_refines
#print axioms c_five_refines
end BB6.Agent5Q0151SourceActions10

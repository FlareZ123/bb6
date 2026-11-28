import Q0151B2EvenActionSound
import Q0151PhysicalStackMore
import Q0151SourceActions1

set_option maxHeartbeats 0

/-!
All-length ORIGINAL-MACHINE B2 second-run 4k+4 branch refinement.
The physical macro executes a positive number of genuine primitive
Turing steps and appends 1110 (10)^(2k+1) 11. The finite interpreter
retains the corresponding stay successor for every k, including the
category-8 long-run case, by the proven two-mode saturation law.
-/

namespace BB6.Agent5Q0151SourceActions8
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151ParamSaturation
open BB6.Agent5Q0151B2EvenActionSound
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151SourceActions1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper

theorem alt_eq_altWord (n : Nat) : alt n = altWord n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change [true,false] ++ alt n = [true,false] ++ altWord n
      exact congrArg (fun w : List Bool => [true,false] ++ w) ih

theorem b_two_zero_refines (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig (1::(4*n+3)::rest)) ≠ 0) :
    Action.stay
      (co true (s ++ [true,true,true,false] ++ alt (2*n+1) ++ [true,true])
        rest) ∈
      delta (co true s (1::(4*n+3)::rest)) ∧
    Goes (boundary 1 s stack (runBits (1::(4*n+3)::rest)))
      (boundary 1
        (s ++ [true,true,true,false] ++ alt (2*n+1) ++ [true,true])
        stack (runBits rest)) := by
  have hlow := segAppend_lower emptySegment
    (by decide) (by decide) s
  have haction := b2_even_action (segAppend emptySegment s)
    hlow.1 hlow.2 n rest hlive
  constructor
  · simpa [co,segAppend_append,alt_eq_altWord,List.append_assoc]
      using haction
  · simpa [runBits] using b_two_zero n s stack (runBits rest)

#print axioms alt_eq_altWord
#print axioms b_two_zero_refines
end BB6.Agent5Q0151SourceActions8

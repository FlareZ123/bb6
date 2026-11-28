import Q0151SourceActions8
import Q0151B2OddActionSound
import Q0151MacroTransfer
import Q0151SourceActions3
import Q0151PackedRightExt
import Q0151BlankStackMore

set_option maxHeartbeats 0

/-!
All-length ORIGINAL-MACHINE B2 second-run 4k+5 branch refinement.
For every physical scannable current segment and saved stack (including
the implicit blank exterior), the authentic positive-length primitive
machine macro transfers s ++ 1110 (10)^(2k+1) 1 and pops. Its packed
right word is canonically decoded, and the finite interpreter emits
exactly its right-summary .pop request. The subsequent restored physical
segment has the exact finite resume summary.
-/

namespace BB6.Agent5Q0151SourceActions9
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151ParamSaturation
open BB6.Agent5Q0151B2OddActionSound
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151SourceActions8
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper

theorem b_two_big_one_source (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (R : List Bool)
    (hs : Scan s.reverse) :
    Goes (boundary 1 s stack (rr 2 (rr (4*n+5) R)))
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack)
        (s ++ [true,true,true,false] ++ alt (2*n+1) ++ true::R)) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail] using
        (b_two_big_one_empty n s R hs)
  | cons saved remaining =>
      simpa [popSaved,popTail] using
        (b_two_big_one_pop n s saved remaining R hs)

theorem b_two_big_one_refines (n : Nat) (s : List Bool)
    (hs : SegGood s) (stack : List (List Bool))
    (rest : List Nat)
    (hlive : rightType (rightSig (1::(4*n+4)::rest)) ≠ 0) :
    ∃ decoded : List Nat,
      Action.pop (rightSig decoded) ∈
        delta (co true s (1::(4*n+4)::rest)) ∧
      Goes (boundary 1 s stack (runBits (1::(4*n+4)::rest)))
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits decoded)) ∧
      resume (rightSig decoded)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) decoded := by
  obtain ⟨decoded,hpack,hsig⟩ :=
    pop_repaired_transfer s hs (2*n+1) rest
  have hlow := segAppend_lower emptySegment
    (by decide) (by decide) s
  have haction := b2_odd_action (segAppend emptySegment s)
    hlow.1 hlow.2 n rest hlive
  have hrequest :
      segConcat (segAppend (segAppend emptySegment s)
        ([true,true,true,false] ++ altWord (2*n+1) ++ [true]))
        (rightSig rest) = rightSig decoded := by
    simpa [alt_eq_altWord] using hsig
  have hact : Action.pop (rightSig decoded) ∈
      delta (co true s (1::(4*n+4)::rest)) := by
    rw [← hrequest]
    simpa [co,mkControl] using haction
  have hmacro := b_two_big_one_source n s stack (runBits rest) hs.1
  have hp : pack (s ++ [true,true,true,false] ++
      alt (2*n+1) ++ true::runBits rest) =
      pack (runBits decoded) := by
    simpa [List.append_assoc] using hpack
  have hright :
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack)
        (s ++ [true,true,true,false] ++ alt (2*n+1) ++
          true::runBits rest) =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp
  rw [hright] at hmacro
  refine ⟨decoded,hact,?_,resume_saved (popSaved stack) decoded⟩
  simpa [runBits] using hmacro

#print axioms b_two_big_one_source
#print axioms b_two_big_one_refines
end BB6.Agent5Q0151SourceActions9

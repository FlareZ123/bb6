import Q0151SourceActions3
import Q0151BlankStackMore

set_option maxHeartbeats 0

/-!
The missing original-source C-mode length-two branch of q0-151.
Unlike B2, C2 pops immediately, transferring the whole current segment
and one final one into the right word.  This handles an arbitrary
run-sequence tail, arbitrary physical saved stack (including the
implicit infinite-zero exterior), and produces the exact executable
finite-interpreter pop request.  No finite invariant is assumed.
-/

namespace BB6.Agent5Q0151SourceActions12
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3

theorem c_two_source (s : List Bool) (stack : List (List Bool))
    (R : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 2 s stack (rr 2 R))
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (s ++ true::R)) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail,alt] using (c_even_empty 0 s R hs)
  | cons saved remaining =>
      simpa [popSaved,popTail,alt] using
        (c_even_pop 0 s saved remaining R hs)

theorem c_two_refines (s : List Bool) (hs : SegGood s)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig (1::rest)) ≠ 0) :
    ∃ decoded : List Nat,
      Action.pop (rightSig decoded) ∈ delta (co false s (1::rest)) ∧
      Goes (boundary 2 s stack (runBits (1::rest)))
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits decoded)) ∧
      resume (rightSig decoded)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) decoded := by
  obtain ⟨decoded,hpack,hsig⟩ :=
    pop_alternating_transfer s hs 0 rest
  have hrequest :
      segConcat (segAppend (segAppend emptySegment s) [true])
        (rightSig rest) = rightSig decoded := by
    simpa [alt,altWord] using hsig
  have hcut : (2,rightSig rest) ∈ cut (rightSig (1::rest)) := by
    simpa [actualNext,cat] using cut_real_next (1::rest) hlive
  have hact : Action.pop (rightSig decoded) ∈
      delta (co false s (1::rest)) := by
    apply action_of_cut _ 2 (rightSig rest) _
      (by simpa [co] using hcut)
    rw [← hrequest]
    simp [actionsFor,choicesA,co,altWord]
  have hmacro := c_two_source s stack (runBits rest) hs.1
  have hp : pack (s ++ true::runBits rest) =
      pack (runBits decoded) := by
    simpa [alt,List.append_assoc] using hpack
  have hright :
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (s ++ true::runBits rest) =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp
  rw [hright] at hmacro
  refine ⟨decoded,hact,?_,resume_saved (popSaved stack) decoded⟩
  simpa [runBits] using hmacro

#print axioms c_two_source
#print axioms c_two_refines
end BB6.Agent5Q0151SourceActions12

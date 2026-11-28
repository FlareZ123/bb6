import Q0151SourceActions2
import Q0151BlankStackMore
import Q0151MacroTransfer

set_option maxHeartbeats 0

/-!
Original-source C6 is a physical marker-stack pop. The empty-stack exterior
is handled by the actual packed source lemma. Both cases normalize the
transferred right word and refine the same finite .pop request.
-/

namespace BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions2

def popSaved : List (List Bool) → List Bool
  | [] => []
  | x::_ => x

def popTail : List (List Bool) → List (List Bool)
  | [] => []
  | _::xs => xs

theorem c_six_source (s : List Bool) (stack : List (List Bool))
    (R : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 2 s stack (rr 6 R))
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (s ++ alt 2 ++ true::R)) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail,List.nil_append] using
        (c_even_empty 1 s R hs)
  | cons saved remaining =>
      simpa [popSaved,popTail] using
        (c_even_pop 1 s saved remaining R hs)

theorem resume_saved (saved : List Bool) (r : List Nat) :
    resume (rightSig r) (segAppend emptySegment saved) =
      co true (saved ++ [true,true,true,true]) r := by
  simp [resume,co,segAppend_append]

theorem c_six_refines (s : List Bool) (hs : SegGood s)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig (5::rest)) ≠ 0) :
    ∃ canonical : List Nat,
      Action.pop (rightSig canonical) ∈ delta (co false s (5::rest)) ∧
      Goes (boundary 2 s stack (runBits (5::rest)))
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits canonical)) ∧
      resume (rightSig canonical)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) canonical := by
  obtain ⟨canonical,hpack,hsummary⟩ :=
    pop_alternating_transfer s hs 2 rest
  have hrequest : rightSig canonical =
      segConcat (segAppend (segAppend emptySegment s)
        (altWord 2 ++ [true])) (rightSig rest) := by
    rw [← alt_two]
    exact hsummary.symm
  have hact : Action.pop (rightSig canonical) ∈
      delta (co false s (5::rest)) := by
    apply action_of_cut _ 6 (rightSig rest) _
      (by simpa [co] using cut_n6 rest hlive)
    rw [hrequest]
    simp [actionsFor,choicesA,co]
  have hmacro := c_six_source s stack (runBits rest) hs.1
  have hpacked : boundary 1 (popSaved stack ++ [true,true,true,true])
      (popTail stack) (s ++ alt 2 ++ true::runBits rest) =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits canonical) := by
    apply boundary_right_pack
    simpa [List.append_assoc] using hpack
  rw [hpacked] at hmacro
  refine ⟨canonical,hact,?_,resume_saved (popSaved stack) canonical⟩
  simpa [runBits] using hmacro

#print axioms c_six_source
#print axioms resume_saved
#print axioms c_six_refines
end BB6.Agent5Q0151SourceActions3

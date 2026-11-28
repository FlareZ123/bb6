import Q0151SourceActions6
import Q0151NestedRightCut
import Q0151MacroTransfer

set_option maxHeartbeats 0

/-!
Exact original-source refinement of the exceptional B2 nested-cut
second-run length 1. The concrete source executes a positive number of
primitive steps, physically transfers the current segment plus 111, and
pops a saved segment (or its blank-exterior equivalent). The abstract
interpreter chooses that same second run from its actual nested cut,
performs precisely the corresponding .pop request, and the resumed
finite control equals the concrete successor's signature.
No finite search or candidate-specific trace length is assumed.
-/

namespace BB6.Agent5Q0151SourceActions7
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151NestedRightCut
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151Category
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

theorem b_two_one_action (s : List Bool) (rest : List Nat)
    (hlive : rightType (rightSig (1::0::rest)) ≠ 0) :
    Action.pop (segConcat
      (segAppend (segAppend emptySegment s) [true,true,true])
        (rightSig rest)) ∈ delta (co true s (1::0::rest)) := by
  have hh := b_two_nested 0 rest hlive
  have hfirst : (2,rightSig (0::rest)) ∈
      cut (rightSig (1::0::rest)) := hh.1
  have hsecond : (1,rightSig rest) ∈ cut (rightSig (0::rest)) := by
    simpa [actualNext,BB6.Agent5Q0151Category.cat] using hh.2
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(2,rightSig (0::rest)), by simpa [co] using hfirst, ?_⟩
  simp [actionsFor,choicesA,co]
  exact ⟨1,rightSig rest,hsecond,by simp⟩

theorem b_two_one_source (s : List Bool) (stack : List (List Bool))
    (R : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s stack (rr 2 (rr 1 R)))
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (s ++ [true,true,true] ++ R)) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail] using b_two_one_empty s R hs
  | cons saved remaining =>
      simpa [popSaved,popTail] using
        (b_two_one_pop s saved remaining R hs)

theorem b_two_one_refines (s : List Bool) (hs : SegGood s)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig (1::0::rest)) ≠ 0) :
    ∃ decoded : List Nat,
      Action.pop (rightSig decoded) ∈
        delta (co true s (1::0::rest)) ∧
      Goes (boundary 1 s stack (runBits (1::0::rest)))
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits decoded)) ∧
      resume (rightSig decoded)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) decoded := by
  obtain ⟨decoded,hpack,hsig⟩ :=
    append_transfer s [true,true,true] hs good_ones_three rest
  have hact : Action.pop (rightSig decoded) ∈
      delta (co true s (1::0::rest)) := by
    rw [← hsig]
    exact b_two_one_action s rest hlive
  have hmacro := b_two_one_source s stack (runBits rest) hs.1
  have hp : pack (s ++ [true,true,true] ++ runBits rest) =
      pack (runBits decoded) := by
    simpa [List.append_assoc] using hpack
  have hright : boundary 1 (popSaved stack ++ [true,true,true,true])
      (popTail stack) (s ++ [true,true,true] ++ runBits rest) =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp
  rw [hright] at hmacro
  refine ⟨decoded,hact,?_,resume_saved (popSaved stack) decoded⟩
  simpa [runBits] using hmacro

#print axioms b_two_one_action
#print axioms b_two_one_source
#print axioms b_two_one_refines
end BB6.Agent5Q0151SourceActions7

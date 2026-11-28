import Q0151SourceActions3
import Q0151BlankStackMore
import Q0151PackedRightExt

set_option maxHeartbeats 0

/-!
The B-mode empty-right original-machine pop is independent of the
current segment length. All source-scannable physical segments are
exactly decoded by the finite segConcat parser, so the physical pop
also implements the interpreter's c=0 .pop action. Empty physical
saved stacks are treated via real zero-padding, not an assumed symbol.
-/

namespace BB6.Agent5Q0151SourceActions6
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151PackedRightExt
open BB6Coverage.Agent13PackedZipper
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3

theorem b_end_source (s : List Bool) (stack : List (List Bool))
    (hs : Scan s.reverse) :
    Goes (boundary 1 s stack [])
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) s) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail,List.nil_append] using b_end_empty s hs
  | cons saved remaining =>
      simpa [popSaved,popTail] using b_end_pop s saved remaining hs

theorem b_end_refines (s : List Bool) (hs : SegGood s)
    (stack : List (List Bool)) :
    ∃ decoded : List Nat,
      Action.pop (rightSig decoded) ∈ delta (co true s []) ∧
      Goes (boundary 1 s stack [])
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits decoded)) ∧
      resume (rightSig decoded)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) decoded := by
  obtain ⟨decoded,hpack,hsig⟩ := transfer_word s hs []
  have hrequest : rightSig decoded =
      segConcat (segAppend emptySegment s) emptyRight := by
    rw [← hsig]
    rfl
  have hact : Action.pop (rightSig decoded) ∈ delta (co true s []) := by
    rw [hrequest]
    simp [delta,co,actionsFor,choicesA,cut,rightSig,emptyRight]
  have hmacro := b_end_source s stack hs.1
  have hp : pack s = pack (runBits decoded) := by
    simpa [runBits] using hpack
  have hright : boundary 1 (popSaved stack ++ [true,true,true,true])
      (popTail stack) s =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp
  rw [hright] at hmacro
  exact ⟨decoded,hact,hmacro,
    resume_saved (popSaved stack) decoded⟩

#print axioms b_end_source
#print axioms b_end_refines
end BB6.Agent5Q0151SourceActions6

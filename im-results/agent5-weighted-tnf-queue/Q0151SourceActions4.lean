import Q0151SourceActions3
import Q0151BlankStackMore
import Q0151MacroTransfer

set_option maxHeartbeats 0

/-!
q0-151's exceptional B2/end-of-right source repair performs a physical
pop and transfers the current segment plus four ones. This original source
execution matches the finite nested-cut .pop including blank exterior.
-/

namespace BB6.Agent5Q0151SourceActions4
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3

theorem b_two_end_source (s : List Bool) (stack : List (List Bool))
    (hs : Scan s.reverse) :
    Goes (boundary 1 s stack (rr 2 []))
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (s ++ [true,true,true,true])) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail] using b_two_end_empty s hs
  | cons saved remaining =>
      simpa [popSaved,popTail] using
        (b_two_end_pop s saved remaining hs)

theorem b_two_end_refines (s : List Bool) (hs : SegGood s)
    (stack : List (List Bool)) :
    ∃ canonical : List Nat,
      Action.pop (rightSig canonical) ∈ delta (co true s [1]) ∧
      Goes (boundary 1 s stack (runBits [1]))
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits canonical)) ∧
      resume (rightSig canonical)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) canonical := by
  obtain ⟨canonical,hpack,hsummary⟩ :=
    pop_four_transfer s hs []
  have hact : Action.pop (rightSig canonical) ∈ delta (co true s [1]) := by
    rw [← hsummary]
    simp [delta,co,actionsFor,choicesA,cut,rightSig,cat,emptyRight]
  have hmacro := b_two_end_source s stack hs.1
  have hpacked : boundary 1 (popSaved stack ++ [true,true,true,true])
      (popTail stack) (s ++ [true,true,true,true]) =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits canonical) := by
    apply boundary_right_pack
    simpa [runBits,List.append_assoc] using hpack
  rw [hpacked] at hmacro
  exact ⟨canonical,hact,by simpa [runBits] using hmacro,
    resume_saved (popSaved stack) canonical⟩

#print axioms b_two_end_source
#print axioms b_two_end_refines
end BB6.Agent5Q0151SourceActions4

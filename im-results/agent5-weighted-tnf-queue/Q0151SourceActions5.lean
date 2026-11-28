import Q0151CEndPhysicalBridge
import Q0151SourceActions3
import Q0151BlankStackMore

set_option maxHeartbeats 0

/-!
Original-machine C-mode end-of-right pop, including implicit blank marker
stack. This is a source-to-finite action refinement valid for EVERY
scannable physical segment with abstract last-run category 3. The genuinely
nontrivial bridge is c_end_trim_exact: its finite category precondition
recovers exactly the three concrete one-bits required by the original
source macro, and trimming one bit changes precisely last:=2.
-/

namespace BB6.Agent5Q0151SourceActions5
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151CEndPhysicalBridge
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151StackSaturation

theorem c_end_source (pref : List Bool) (stack : List (List Bool))
    (hpref : Scan pref.reverse) :
    Goes (boundary 2 (pref ++ [true]) stack [])
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) pref) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail,List.nil_append] using
        (c_end_empty pref hpref)
  | cons saved remaining =>
      simpa [popSaved,popTail] using
        (c_end_pop pref saved remaining hpref)

theorem c_end_refines (s : List Bool) (hs : SegGood s)
    (h3 : (segAppend emptySegment s).last = 3)
    (stack : List (List Bool)) :
    ∃ decoded : List Nat,
      Action.pop (rightSig decoded) ∈ delta (co false s []) ∧
      Goes (boundary 2 s stack [])
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits decoded)) ∧
      resume (rightSig decoded)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) decoded := by
  obtain ⟨pref,hsplit,hgood,hsummary⟩ :=
    c_end_trim_exact s hs h3
  obtain ⟨decoded,hpack,hsig⟩ := transfer_word pref hgood []
  have hrequest : rightSig decoded =
      segConcat {segAppend emptySegment s with last := 2} emptyRight := by
    rw [← hsig,hsummary]
    rfl
  have hact : Action.pop (rightSig decoded) ∈
      delta (co false s []) := by
    rw [hrequest]
    simp [delta,co,actionsFor,choicesA,cut,rightSig,emptyRight,h3]
  have hmacro : Goes (boundary 2 s stack [])
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) pref) := by
    rw [hsplit]
    exact c_end_source pref stack hgood.1
  have hp : pack pref = pack (runBits decoded) := by
    simpa [runBits] using hpack
  have hright : boundary 1 (popSaved stack ++ [true,true,true,true])
      (popTail stack) pref =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp
  rw [hright] at hmacro
  exact ⟨decoded,hact,hmacro,
    resume_saved (popSaved stack) decoded⟩

#print axioms c_end_source
#print axioms c_end_refines
end BB6.Agent5Q0151SourceActions5

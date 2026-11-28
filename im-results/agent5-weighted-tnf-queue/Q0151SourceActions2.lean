import Q0151SourceActions1
import Q0151MacroTransfer
import Q0151PackedRightExt

set_option maxHeartbeats 0

/-!
q0-151's positive B-even source branch consumes a run of six ones,
returns a new right word prefixed by 101, and grows the current left
segment by four ones. That right word is NOT necessarily a canonical
one-run list. The canonicalization below is constructive at the level of
the original packed Turing machine and matches exactly the finite
interpreter's prepend action. It is the first q0-151 branch requiring
both physical semantics and unbounded right-word transfer.
-/

namespace BB6.Agent5Q0151SourceActions2
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151Category

theorem cut_n6 (rest : List Nat)
    (h : rightType (rightSig (5::rest)) ≠ 0) :
    (6,rightSig rest) ∈ cut (rightSig (5::rest)) := by
  simpa [cat,actualNext] using cut_real_next (5::rest) h

theorem b_six_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat)
    (hlive : rightType (rightSig (5::rest)) ≠ 0) :
    ∃ canonical : List Nat,
      Action.stay (co true (s++[true,true,true,true]) canonical) ∈
        delta (co true s (5::rest)) ∧
      Goes (boundary 1 s stack (runBits (5::rest)))
        (boundary 1 (s++[true,true,true,true])
          stack (runBits canonical)) := by
  obtain ⟨canonical,hpack,hsummary⟩ :=
    transfer_word (alt 1 ++ [true]) (good_alt_one 1) rest
  have hsig : rightSig canonical =
      prepend (altWord 1 ++ [true]) (rightSig rest) := by
    unfold prepend
    rw [← alt_one]
    exact hsummary.symm
  have hco : co true (s++[true,true,true,true]) canonical =
      ⟨true,prepend (altWord 1 ++ [true]) (rightSig rest),
        segAppend (segAppend emptySegment s) [true,true,true,true]⟩ := by
    simp [co_extend,hsig]
  have hact : Action.stay
      (co true (s++[true,true,true,true]) canonical) ∈
        delta (co true s (5::rest)) := by
    apply action_of_cut _ 6 (rightSig rest) _
      (by simpa [co] using cut_n6 rest hlive)
    rw [hco]
    simp [actionsFor,choicesA,co]
  have hmacro := b_even_big 0 s stack (runBits rest)
  have hpacked : boundary 1 (s++[true,true,true,true]) stack
      (alt 1 ++ true::runBits rest) =
      boundary 1 (s++[true,true,true,true]) stack
        (runBits canonical) := by
    apply boundary_right_pack
    simpa [List.append_assoc] using hpack
  rw [hpacked] at hmacro
  exact ⟨canonical,hact,by simpa [runBits] using hmacro⟩

#print axioms cut_n6
#print axioms b_six_refines
end BB6.Agent5Q0151SourceActions2

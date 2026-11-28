import Q0151SourceActions10
import Q0151SourceActions3
import Q0151OuterAbstractActions
import Q0151MacroTransfer
import Q0151PackedRightExt
import Q0151BlankStackMore

set_option maxHeartbeats 0

/-!
All-length ORIGINAL-MACHINE B/C runs 4k+6: B prepends an alternating
physical right word and stays in B after adding four ones; C physically
pops one saved segment and transfers the current segment plus an
alternating physical word to the right. The exact finite interpreter
action is certified for every k≥0 by source-independent run saturation.
Here both source branches are reconciled with canonical packed right
words and the finite transition request, including zero-filled
empty-stack exterior. Every Goes witness is an actual positive-length
primitive execution of q0-151, not a macro simulator conjecture.
-/

namespace BB6.Agent5Q0151SourceActions11
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151ParamSaturation
open BB6.Agent5Q0151OuterAbstractActions
open BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151SourceActions8
open BB6.Agent5Q0151SegmentRunSound
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper

theorem b_six_refines (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (rest : List Nat)
    (hlive : rightType (rightSig ((4*n+5)::rest)) ≠ 0) :
    ∃ decoded : List Nat,
      Action.stay (co true (s++[true,true,true,true]) decoded) ∈
        delta (co true s ((4*n+5)::rest)) ∧
      Goes (boundary 1 s stack (runBits ((4*n+5)::rest)))
        (boundary 1 (s++[true,true,true,true])
          stack (runBits decoded)) := by
  obtain ⟨decoded,hpack,hsig⟩ :=
    transfer_word (alt (2*n+1) ++ [true])
      (good_alt_one (2*n+1)) rest
  have hreq : prepend (altWord (2*n+1) ++ [true])
      (rightSig rest) = rightSig decoded := by
    unfold prepend
    simpa [alt_eq_altWord] using hsig
  have ha := b_six_stay (segAppend emptySegment s) n rest hlive
  have hact : Action.stay
      (co true (s++[true,true,true,true]) decoded) ∈
      delta (co true s ((4*n+5)::rest)) := by
    rw [hreq] at ha
    simpa [co,mkControl,segAppend_append] using ha
  have hmacro := b_even_big n s stack (runBits rest)
  have hp : pack (alt (2*n+1) ++ true::runBits rest) =
      pack (runBits decoded) := by
    simpa [List.append_assoc] using hpack
  have hright :
      boundary 1 (s++[true,true,true,true]) stack
        (alt (2*n+1) ++ true::runBits rest) =
      boundary 1 (s++[true,true,true,true]) stack
        (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp
  rw [hright] at hmacro
  exact ⟨decoded,hact,by simpa [runBits,Nat.mul_add,Nat.add_assoc]
    using hmacro⟩

theorem c_six_source (n : Nat) (s : List Bool)
    (stack : List (List Bool)) (R : List Bool)
    (hs : Scan s.reverse) :
    Goes (boundary 2 s stack (rr (4*(n+1)+2) R))
      (boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (s ++ alt (2*(n+1)) ++ true::R)) := by
  cases stack with
  | nil =>
      simpa [popSaved,popTail] using
        (c_even_empty (n+1) s R hs)
  | cons saved remaining =>
      simpa [popSaved,popTail] using
        (c_even_pop (n+1) s saved remaining R hs)

theorem c_six_refines (n : Nat) (s : List Bool)
    (hs : SegGood s) (stack : List (List Bool))
    (rest : List Nat)
    (hlive : rightType (rightSig ((4*n+5)::rest)) ≠ 0) :
    ∃ decoded : List Nat,
      Action.pop (rightSig decoded) ∈
        delta (co false s ((4*n+5)::rest)) ∧
      Goes (boundary 2 s stack (runBits ((4*n+5)::rest)))
        (boundary 1 (popSaved stack ++ [true,true,true,true])
          (popTail stack) (runBits decoded)) ∧
      resume (rightSig decoded)
        (segAppend emptySegment (popSaved stack)) =
          co true (popSaved stack ++ [true,true,true,true]) decoded := by
  obtain ⟨decoded,hpack,hsig⟩ :=
    pop_alternating_transfer s hs (2*n+2) rest
  have hlow := segAppend_lower emptySegment
    (by decide) (by decide) s
  have ha := c_six_pop (segAppend emptySegment s)
    hlow.1 hlow.2 n rest hlive
  have hrequest : segConcat
      (segAppend (segAppend emptySegment s)
        (altWord (2*n+2) ++ [true])) (rightSig rest) =
      rightSig decoded := by
    simpa [alt_eq_altWord] using hsig
  have hact : Action.pop (rightSig decoded) ∈
      delta (co false s ((4*n+5)::rest)) := by
    rw [← hrequest]
    simpa [co,mkControl] using ha
  have hmacro := c_six_source n s stack (runBits rest) hs.1
  have hp : pack (s ++ alt (2*n+2) ++ true::runBits rest) =
      pack (runBits decoded) := by
    simpa [List.append_assoc] using hpack
  have hp' : pack (s ++ alt (2*(n+1)) ++ true::runBits rest) =
      pack (runBits decoded) := by
    simpa [Nat.mul_add,Nat.add_assoc] using hp
  have hright :
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack)
        (s ++ alt (2*(n+1)) ++ true::runBits rest) =
      boundary 1 (popSaved stack ++ [true,true,true,true])
        (popTail stack) (runBits decoded) :=
    boundary_right_pack _ _ _ _ _ hp'
  rw [hright] at hmacro
  refine ⟨decoded,hact,?_,resume_saved (popSaved stack) decoded⟩
  simpa [runBits,Nat.mul_add,Nat.add_assoc] using hmacro

#print axioms b_six_refines
#print axioms c_six_source
#print axioms c_six_refines
end BB6.Agent5Q0151SourceActions11

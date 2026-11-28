import Q0151TransferredWord
import Q0151SegmentGrammar

set_option maxHeartbeats 0

/-!
The exact q0-151 source macros append only a handful of segment suffix
shapes. These lemmas show that the arbitrary-length alternation and the
two special repair suffixes are in the source Scan language and that every
macro pop transfer, even with a concrete saved-stack payload, is reflected
by segConcat on the finite summary.
No finite certificate is assumed in these algebraic statements.
-/

namespace BB6.Agent5Q0151MacroTransfer
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151SegmentRunSound
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper

theorem good_alt_one (n : Nat) : SegGood (alt n ++ [true]) := by
  refine ⟨?_,⟨alt n,rfl⟩⟩
  simpa [List.reverse_append,alt_reverse] using
    (Scan.one (scanAlt n))

theorem good_two_zero_one (n : Nat) :
    SegGood ([true,true,true,false] ++ alt n ++ [true]) := by
  have ht : Scan ([false,true,true,true] : List Bool) :=
    Scan.pair (Scan.one (Scan.one Scan.nil))
  have hr : Scan ([true] ++ revAlt n ++ [false,true,true,true]) :=
    Scan.one (Scan.append (scanAlt n) ht)
  refine ⟨?_,⟨[true,true,true,false] ++ alt n, by simp [List.append_assoc]⟩⟩
  simpa [List.reverse_append,alt_reverse,List.append_assoc] using hr

theorem good_append_alt_one (s : List Bool) (hs : SegGood s) (n : Nat) :
    SegGood (s ++ alt n ++ [true]) := by
  simpa [List.append_assoc] using good_append hs (good_alt_one n)

theorem good_append_two_zero_one (s : List Bool)
    (hs : SegGood s) (n : Nat) :
    SegGood (s ++ [true,true,true,false] ++ alt n ++ [true]) := by
  simpa [List.append_assoc] using good_append hs (good_two_zero_one n)

theorem append_transfer (s ext : List Bool) (hs : SegGood s)
    (he : SegGood ext) (right : List Nat) :
    ∃ decoded : List Nat,
      pack ((s++ext) ++ runBits right) = pack (runBits decoded) ∧
      segConcat (segAppend (segAppend emptySegment s) ext)
        (rightSig right) = rightSig decoded := by
  obtain ⟨decoded,hpack,hsig⟩ :=
    transfer_word (s++ext) (good_append hs he) right
  refine ⟨decoded,hpack,?_⟩
  simpa only [BB6.Agent5Q0151SegmentRunSound.segAppend_append] using hsig

theorem pop_four_transfer (s : List Bool) (hs : SegGood s)
    (right : List Nat) :
    ∃ decoded : List Nat,
      pack ((s++[true,true,true,true]) ++ runBits right) =
        pack (runBits decoded) ∧
      segConcat (segAppend (segAppend emptySegment s)
        [true,true,true,true]) (rightSig right) =
        rightSig decoded := by
  exact append_transfer s [true,true,true,true] hs good_ones_four right

theorem pop_alternating_transfer (s : List Bool) (hs : SegGood s)
    (n : Nat) (right : List Nat) :
    ∃ decoded : List Nat,
      pack ((s ++ alt n ++ [true]) ++ runBits right) =
        pack (runBits decoded) ∧
      segConcat (segAppend (segAppend emptySegment s)
        (alt n ++ [true])) (rightSig right) =
        rightSig decoded := by
  simpa only [List.append_assoc] using
    (append_transfer s (alt n ++ [true]) hs (good_alt_one n) right)

theorem pop_repaired_transfer (s : List Bool) (hs : SegGood s)
    (n : Nat) (right : List Nat) :
    ∃ decoded : List Nat,
      pack ((s ++ [true,true,true,false] ++ alt n ++ [true]) ++
          runBits right) = pack (runBits decoded) ∧
      segConcat (segAppend (segAppend emptySegment s)
        ([true,true,true,false] ++ alt n ++ [true]))
        (rightSig right) = rightSig decoded := by
  simpa only [List.append_assoc] using
    (append_transfer s
      ([true,true,true,false] ++ alt n ++ [true])
        hs (good_two_zero_one n) right)

#print axioms good_alt_one
#print axioms good_two_zero_one
#print axioms append_transfer
#print axioms pop_four_transfer
#print axioms pop_alternating_transfer
#print axioms pop_repaired_transfer
end BB6.Agent5Q0151MacroTransfer

import Q0151TransferredWord
import Q0151PhysicalStack

set_option maxHeartbeats 0

/-!
The original q0-151 physical boundary packs its head and tail separately.
A Boolean list is not a canonical tape representation because trailing
zero cells are implicit. Equal packed right words nevertheless induce
exactly the same original P configuration, not merely the same total
number of set bits. This transports the all-length stack-pop transfer
word theorem into the original source machine representation.
-/

namespace BB6.Agent5Q0151PackedRightExt
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151FiniteModel
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

theorem pack_head_tail (R T : List Bool)
    (he : pack R = pack T) :
    R.headD false = T.headD false ∧
      pack R.tail = pack T.tail := by
  have hR : pack R = (R.headD false).toNat + 2 * pack R.tail := by
    cases R <;> rfl
  have hT : pack T = (T.headD false).toNat + 2 * pack T.tail := by
    cases T <;> rfl
  have hsum : (R.headD false).toNat + 2 * pack R.tail =
      (T.headD false).toNat + 2 * pack T.tail := by
    omega
  have hhead : R.headD false = T.headD false := by
    cases h0 : R.headD false <;> cases h1 : T.headD false <;>
      simp_all [Bool.toNat] <;> omega
  refine ⟨hhead,?_⟩
  rw [hhead] at hsum
  omega

theorem frame_right_pack (q : Fin 6) (left R T : List Bool)
    (he : pack R = pack T) :
    frame q left R = frame q left T := by
  obtain ⟨hhead,htail⟩ := pack_head_tail R T he
  unfold frame encode0
  simp [hhead,htail]

theorem boundary_right_pack (q : Fin 6) (left : List Bool)
    (stack : List (List Bool)) (R T : List Bool)
    (he : pack R = pack T) :
    boundary q left stack R = boundary q left stack T := by
  exact frame_right_pack q (leftOf left stack) R T he

theorem transferred_boundary (q : Fin 6) (left : List Bool)
    (stack : List (List Bool)) (s : List Bool) (hs : SegGood s)
    (right : List Nat) :
    ∃ decoded : List Nat,
      boundary q left stack (s ++ runBits right) =
        boundary q left stack (runBits decoded) ∧
      segConcat (segAppend emptySegment s) (rightSig right) =
        rightSig decoded := by
  obtain ⟨decoded,hpack,hsummary⟩ := transfer_word s hs right
  exact ⟨decoded,boundary_right_pack q left stack
    (s ++ runBits right) (runBits decoded) hpack,hsummary⟩

#print axioms pack_head_tail
#print axioms frame_right_pack
#print axioms boundary_right_pack
#print axioms transferred_boundary
end BB6.Agent5Q0151PackedRightExt

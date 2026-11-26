import WeightedBoxOneHalt
import Raw10EncodedSourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13.Box15

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge BB6.Agent17Raw10BoxFar BB6.Agent13BoxOneHalt

def encodedDomain : Box Slot Transition :=
  fun s => (BB6.Agent49BoxEncoded.boxes[15]! (slotIndex s)).map decodeCode

theorem sourceDomainEq : raw10Remainder[15]! = encodedDomain := by
  funext s
  exact exact_box_at_index (15 : Fin 34) s

def fallback : Slot → Move := fun _ => ⟨true,false,0⟩

theorem fallback_valid (s : Slot) :
    none ∈ raw10Remainder[15]! s → some (fallback s) ∈ raw10Remainder[15]! s := by
  rw [sourceDomainEq]
  rcases s with ⟨q,b⟩
  revert q b
  decide

/-- Bounding six nonempty one-halt slices suffices for the full
    source rectangle, with the exact blank-delay weighting. -/
theorem sourceSlices_iff (B : Nat) :
    (∀ m, Fits raw10Remainder[15]! m → WeightedBound B m) ↔
      (∀ s m, Fits (haltSlice raw10Remainder[15]! s) m → WeightedBound B m) :=
  oneHaltSlices_iff _ fallback fallback_valid (fun _ => rfl) B

#print axioms sourceDomainEq
#print axioms fallback_valid
#print axioms sourceSlices_iff

end BB6.Agent13.Box15

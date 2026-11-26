import Box17Direct
import Raw10EncodedSourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13.Box17
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge

theorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by
  revert v
  decide

theorem sourceDomainEq : domain = raw10Remainder[17]! := by
  funext s
  rw [BB6.Agent17Raw10BoxFar.exact_box_at_index (17 : Fin 34) s]
  unfold domain
  rw [literalDomain_matches, index_source]
  have hd : decode = BB6.Agent17Raw10BoxFar.decodeCode := funext decode_source
  rw [hd]

theorem sourceBound_of_r1 (hr1 : NeverHalts r1Machine) (m : Machine)
    (hm : Fits raw10Remainder[17]! m) : WeightedBound 7014 m :=
  weighted_of_r1 hr1 m (sourceDomainEq.symm ▸ hm)

theorem sourceExact_of_r1 (hr1 : NeverHalts r1Machine) (B : Nat) :
    (∀ m, Fits raw10Remainder[17]! m → WeightedBound B m) ↔ 7014 ≤ B := by
  rw [← sourceDomainEq]
  exact exactWeighted_of_r1 hr1 B

#print axioms sourceDomainEq
#print axioms sourceExact_of_r1
end BB6.Agent13.Box17

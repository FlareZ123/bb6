import Box16Direct
import Raw10EncodedSourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13.Box16
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent13.Box17 BB6.Agent49BoxBridge BB6.Agent17Raw10BoxFar BB6.Agent50RootFrontier

theorem index_source (s : Slot) : index s = slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem decode_source (v : Fin 25) : decode v = decodeCode v := by
  revert v
  decide

/-- Rectangle 16 is pointwise identical to the source-defined raw10 residual
    at index 16; this is the bridge from the literal finite domain to the
    original parent remainder, not a copied-box assumption. -/
theorem sourceDomainEq : domain = raw10Remainder[16]! := by
  funext s
  have h := exact_box_at_index (16 : Fin 34) s
  change raw10Remainder[16]! s =
    (BB6.Agent49BoxEncoded.boxes[16]! (slotIndex s)).map decodeCode at h
  unfold domain
  rw [← h, literalDomain_matches, index_source]
  have hd : decode = decodeCode := funext decode_source
  rw [hd]

theorem sourceBound (m : Machine) (hm : Fits raw10Remainder[16]! m) :
    WeightedBound 7376 m :=
  weighted m (sourceDomainEq.symm ▸ hm)

theorem sourceExact (B : Nat) :
    (∀ m, Fits raw10Remainder[16]! m → WeightedBound B m) ↔ 7376 ≤ B := by
  rw [← sourceDomainEq]
  exact exactWeighted B

/-- Once the other 33 source residual boxes and the held table are covered,
    rectangle 16 discharges its named raw10 obligation at every B ≥ 7376. -/
theorem raw10_cover_except16 (B : Nat) (hB : 7376 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOther : ∀ r ∈ raw10Remainder, r ≠ raw10Remainder[16]! →
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  raw10_cover B (Nat.le_trans (by decide : 7014 ≤ 7376) hB) hHeld
    (fun r hr m hm => by
      by_cases he : r = raw10Remainder[16]!
      · subst r
        intro k d hk hd
        exact Nat.le_trans (sourceBound m hm k d hk hd) hB
      · exact hOther r hr he m hm)

#print axioms sourceDomainEq
#print axioms sourceExact
#print axioms raw10_cover_except16
end BB6.Agent13.Box16

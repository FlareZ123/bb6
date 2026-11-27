import Raw10EncodedSourceBridge
import Box17AuditCore
import WeightedSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent17.Box28Symmetry
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode index slot index_slot)
open BB6.Agent16WeightedSymmetry

def efState (q : Fin 6) : Fin 6 := if q = 4 then 5 else if q = 5 then 4 else q

theorem ef_involutive : ∀ q : Fin 6, efState (efState q) = q := by decide

def ef : StatePerm := ⟨efState, efState, ef_involutive, ef_involutive⟩

/-- Exact action on transition codes: swap E and F, not symbols or direction. -/
def efCode (v : Fin 25) : Fin 25 :=
  Fin.ofNat 25 (if 17 ≤ v.val ∧ v.val ≤ 20 then v.val + 4
    else if 21 ≤ v.val then v.val - 4 else v.val)

theorem ef_code_decode : ∀ v : Fin 25,
    (decode v).map (renameMove ef) = decode (efCode v) := by decide

theorem ef_code_involutive : ∀ v : Fin 25, efCode (efCode v) = v := by decide

-- Source override domain; a genuine subrectangle when the fixed codes are admitted.
def sourceCutFor (d0 d1 : Fin 25) : Box Slot Transition := fun s =>
  if index s = 7 then [decode d1] else if index s = 6 then [decode d0]
  else raw10Remainder[28]! s

def baseLiteral (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 2 => [11]
  | 4 => [11]
  | 5 => [13]
  | _ => List.finRange 25

def cutLiteralFor (d0 d1 : Fin 25) (i : Fin 12) : List (Fin 25) :=
  if i = 7 then [d1] else if i = 6 then [d0] else baseLiteral i

def cutDomainFor (d0 d1 : Fin 25) : Box Slot Transition := fun s =>
  (cutLiteralFor d0 d1 (index s)).map decode

theorem base_matches : ∀ i : Fin 12, i ≠ 6 → i ≠ 7 →
    baseLiteral i = BB6.Agent49BoxEncoded.boxes[28]! i := by decide

theorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by
  revert v
  decide

theorem sourceCutFor_eq (d0 d1 : Fin 25) : cutDomainFor d0 d1 = sourceCutFor d0 d1 := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (28 : Fin 34) s
  change raw10Remainder[28]! s =
    (BB6.Agent49BoxEncoded.boxes[28]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  unfold cutDomainFor cutLiteralFor sourceCutFor
  by_cases h7 : index s = 7
  · simp [h7]
  · by_cases h6 : index s = 6
    · simp [h7,h6]
    · simp only [if_neg h7,if_neg h6]
      rw [base_matches _ h6 h7,h,← index_source]
      rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]

-- Check only the fixed background; both selected transitions remain symbolic.
theorem ef_index_D (q : Fin 6) (r : Bool) :
    (index (ef.backward q,r) = 6 ↔ index (q,r) = 6) ∧
    (index (ef.backward q,r) = 7 ↔ index (q,r) = 7) := by
  revert q r
  decide

theorem ef_base_mem (q : Fin 6) (r : Bool) (v : Fin 25)
    (h : v ∈ baseLiteral (index (ef.backward q,r))) :
    efCode v ∈ baseLiteral (index (q,r)) := by
  revert q r v
  decide

theorem ef_cut_mem (d0 d1 : Fin 25) (q : Fin 6) (r : Bool) (v : Fin 25)
    (h : v ∈ cutLiteralFor d0 d1 (index (ef.backward q,r))) :
    efCode v ∈ cutLiteralFor (efCode d0) (efCode d1) (index (q,r)) := by
  obtain ⟨h6,h7⟩ := ef_index_D q r
  by_cases e7 : index (q,r) = 7
  · have a7 := h7.mpr e7
    simp [cutLiteralFor,a7] at h
    simp [cutLiteralFor,e7,h]
  · have a7 : index (ef.backward q,r) ≠ 7 := fun h => e7 (h7.mp h)
    by_cases e6 : index (q,r) = 6
    · have a6 := h6.mpr e6
      simp [cutLiteralFor,a7,a6] at h
      simp [cutLiteralFor,e7,e6,h]
    · have a6 : index (ef.backward q,r) ≠ 6 := fun h => e6 (h6.mp h)
      simp only [cutLiteralFor,if_neg a7,if_neg a6] at h
      simp only [cutLiteralFor,if_neg e7,if_neg e6]
      exact ef_base_mem q r v h

theorem fits_renamed (d0 d1 : Fin 25) (m : Machine)
    (hm : Fits (sourceCutFor d0 d1) m) :
    Fits (sourceCutFor (efCode d0) (efCode d1)) (renameTable ef m) := by
  rw [← sourceCutFor_eq] at hm
  rw [← sourceCutFor_eq]
  intro s
  rcases s with ⟨q,r⟩
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (hm (ef.backward q,r))
  change (m (ef.backward q,r)).map (renameMove ef) ∈ cutDomainFor _ _ (q,r)
  rw [← he,ef_code_decode]
  exact List.mem_map.mpr ⟨efCode v,ef_cut_mem d0 d1 q r v hv,rfl⟩

theorem transportFor (d0 d1 : Fin 25) {B : Nat}
    (hb : ∀ m, Fits (sourceCutFor (efCode d0) (efCode d1)) m → WeightedBound B m) :
    ∀ m, Fits (sourceCutFor d0 d1) m → WeightedBound B m := by
  intro m hm
  exact (weightedBound_rename_iff B ef (by decide) m).mp
    (hb (renameTable ef m) (fits_renamed d0 d1 m hm))

theorem sourceCutFor_fits (d0 d1 : Fin 25) (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (slot 6) = decode d0) (h1 : m (slot 7) = decode d1) :
    Fits (sourceCutFor d0 d1) m := by
  intro s
  unfold sourceCutFor
  by_cases h7 : index s = 7
  · have hs : s = slot 7 := by
      have he := BB6.Agent13.Box17.slot_index s
      rw [h7] at he
      exact he.symm
    simp [hs,index_slot,h1]
  · by_cases h6 : index s = 6
    · have hs : s = slot 6 := by
        have he := BB6.Agent13.Box17.slot_index s
        rw [h6] at he
        exact he.symm
      simp [hs,index_slot,h0]
    · simpa [h7,h6] using hm s

abbrev sourceCut := sourceCutFor 14

theorem sourceCut_fits (d : Fin 25) (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (slot 6) = decode 14) (h1 : m (slot 7) = decode d) :
    Fits (sourceCut d) m := sourceCutFor_fits 14 d m hm h0 h1

#print axioms sourceCutFor_eq
#print axioms ef_cut_mem
#print axioms fits_renamed
#print axioms transportFor
#print axioms sourceCutFor_fits
end BB6.Agent17.Box28Symmetry

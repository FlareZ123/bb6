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

-- The exact source rectangle with D0=14 and one selected D1 transition.
def sourceCut (d1 : Fin 25) : Box Slot Transition := fun s =>
  if index s = 7 then [decode d1] else if index s = 6 then [decode 14]
  else raw10Remainder[28]! s

def baseLiteral (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 2 => [11]
  | 4 => [11]
  | 5 => [13]
  | _ => List.finRange 25

def cutLiteral (d1 : Fin 25) (i : Fin 12) : List (Fin 25) :=
  if i = 7 then [d1] else if i = 6 then [14] else baseLiteral i

def cutDomain (d1 : Fin 25) : Box Slot Transition := fun s =>
  (cutLiteral d1 (index s)).map decode

theorem base_matches : ∀ i : Fin 12, i ≠ 6 → i ≠ 7 →
    baseLiteral i = BB6.Agent49BoxEncoded.boxes[28]! i := by decide

theorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by
  revert v
  decide

theorem sourceCut_eq (d1 : Fin 25) : cutDomain d1 = sourceCut d1 := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (28 : Fin 34) s
  change raw10Remainder[28]! s =
    (BB6.Agent49BoxEncoded.boxes[28]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  unfold cutDomain cutLiteral sourceCut
  by_cases h7 : index s = 7
  · simp [h7]
  · by_cases h6 : index s = 6
    · simp [h7,h6]
    · simp only [if_neg h7,if_neg h6]
      rw [base_matches _ h6 h7,h,← index_source]
      rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]

-- A finite domain-inclusion checker, not a machine simulation.
def RenameOK (a b : Fin 25) : Prop :=
  ∀ (q : Fin 6) (r : Bool) (v : Fin 25),
    v ∈ cutLiteral a (index (ef.backward q,r)) →
    (decode v).map (renameMove ef) ∈ cutDomain b (q,r)

theorem rename_21_17 : RenameOK 21 17 := by unfold RenameOK; decide
theorem rename_22_18 : RenameOK 22 18 := by unfold RenameOK; decide
theorem rename_23_19 : RenameOK 23 19 := by unfold RenameOK; decide
theorem rename_24_20 : RenameOK 24 20 := by unfold RenameOK; decide

theorem fits_renamed {a b : Fin 25} (h : RenameOK a b) (m : Machine)
    (hm : Fits (sourceCut a) m) : Fits (sourceCut b) (renameTable ef m) := by
  rw [← sourceCut_eq a] at hm
  rw [← sourceCut_eq b]
  intro s
  rcases s with ⟨q,r⟩
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (hm (ef.backward q,r))
  change (m (ef.backward q,r)).map (renameMove ef) ∈ cutDomain b (q,r)
  rw [← he]
  exact h q r v hv

theorem transport {a b : Fin 25} {B : Nat} (h : RenameOK a b)
    (hb : ∀ m, Fits (sourceCut b) m → WeightedBound B m) :
    ∀ m, Fits (sourceCut a) m → WeightedBound B m := by
  intro m hm
  exact (weightedBound_rename_iff B ef (by decide) m).mp
    (hb (renameTable ef m) (fits_renamed h m hm))

theorem sourceCut_fits (d : Fin 25) (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (slot 6) = decode 14) (h1 : m (slot 7) = decode d) :
    Fits (sourceCut d) m := by
  intro s
  unfold sourceCut
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

#print axioms sourceCut_eq
#print axioms fits_renamed
#print axioms transport
#print axioms sourceCut_fits
end BB6.Agent17.Box28Symmetry

import Box17AuditCore
import Raw10EncodedSourceBridge
import C9PairWeights

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13.Box3Parent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (index slot decode slot_index index_slot haltBound_sound)
open BB6.Agent13.C9Bridge (table long_halt delays_zero)

def codes : List (Fin 25) :=
  [0,2,3,5,6,7,8,9,10,11,12,14,15,16,17,18,19,20,21,22,23,24]

def branchDomain (c : Fin 25) : Box Slot Transition :=
  fun s => if index s = 5 then [decode c] else raw10Remainder[3]! s

theorem source_C1 : raw10Remainder[3]! (slot 5) = codes.map decode := by
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (3 : Fin 34) (slot 5)
  change raw10Remainder[3]! (slot 5) =
    (BB6.Agent49BoxEncoded.boxes[3]! (BB6.Agent17Raw10BoxFar.slotIndex (slot 5))).map
      BB6.Agent17Raw10BoxFar.decodeCode at h
  rw [h]
  decide

theorem branch_cover (m : Machine) (hm : Fits raw10Remainder[3]! m) :
    ∃ c ∈ codes, Fits (branchDomain c) m := by
  have hmem := hm (slot 5)
  rw [source_C1] at hmem
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hmem
  refine ⟨c,hc,?_⟩
  intro s
  by_cases hi : index s = 5
  · have hs : s = slot 5 := by rw [← slot_index s,hi]
    subst s
    simp [branchDomain,index_slot,he]
  · simpa [branchDomain,hi] using hm s

theorem parent_upper (B : Nat)
    (branches : ∀ c ∈ codes, ∀ m, Fits (branchDomain c) m → WeightedBound B m) :
    ∀ m, Fits raw10Remainder[3]! m → WeightedBound B m := by
  intro m hm
  obtain ⟨c,hc,hfit⟩ := branch_cover m hm
  exact branches c hc m hfit

def c0Table : PartialMachine := fun s =>
  match (index s).val with
  | 0 => some (decode 8)
  | 1 => some (decode 14)
  | 2 => some (decode 11)
  | 3 => some (decode 7)
  | 4 => some (decode 17)
  | 5 => some (decode 0)
  | _ => none

theorem c0_root_eq (s : Slot) : c0Table s =
    (match branchDomain 0 s with | [v] => some v | _ => none) := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem c0_compatible (m : Machine) (hm : Fits (branchDomain 0) m) :
    compatible c0Table m := by
  intro s t ht
  rw [c0_root_eq] at ht
  cases he : branchDomain 0 s with
  | nil => simp [he] at ht
  | cons a as =>
    cases as with
    | nil =>
      have hmem := hm s
      simp [he] at hmem ht
      exact hmem.trans ht
    | cons b bs => simp [he] at ht

theorem c0_bound (m : Machine) (hm : Fits (branchDomain 0) m) :
    WeightedBound 8 m :=
  haltBound_sound c0Table 2 8 (by decide) m (c0_compatible m hm)

theorem long_fits : Fits raw10Remainder[3]! (table false) := by
  intro s
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem parent_lower (B : Nat)
    (h : ∀ m, Fits raw10Remainder[3]! m → WeightedBound B m) :
    3142249368711030 ≤ B := by
  exact h (table false) long_fits 3142249368711029 0 long_halt (by rw [delays_zero]; decide)

theorem parent_exact_if_branches
    (h : ∀ c ∈ codes, ∀ m, Fits (branchDomain c) m → WeightedBound 3142249368711030 m)
    (B : Nat) :
    (∀ m, Fits raw10Remainder[3]! m → WeightedBound B m) ↔ 3142249368711030 ≤ B := by
  constructor
  · exact parent_lower B
  · intro hb m hm k d hk hd
    exact Nat.le_trans (parent_upper _ h m hm k d hk hd) hb

#print axioms branch_cover
#print axioms c0_bound
#print axioms parent_exact_if_branches
end BB6.Agent13.Box3Parent

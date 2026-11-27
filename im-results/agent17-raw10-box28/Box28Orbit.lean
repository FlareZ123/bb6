import Box17AuditCore
import Raw10EncodedSourceBridge
import WeightedTNF
import Box28Simple

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent17.Box28Orbit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (index slot index_slot slot_index decode)

def codes (d1 : Fin 25) (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 2 => [11]
  | 4 => [11]
  | 5 => [13]
  | 6 => [14]
  | 7 => [d1]
  | _ => List.finRange 25

def domain (d1 : Fin 25) : Box Slot Transition := fun s => (codes d1 (index s)).map decode
def sourceDomain (d1 : Fin 25) : Box Slot Transition := fun s =>
  if index s = 7 then [decode d1] else if index s = 6 then [decode 14] else raw10Remainder[28]! s

theorem codes_match (d1 : Fin 25) (i : Fin 12) :
    codes d1 i = if i = 7 then [d1] else if i = 6 then [14] else BB6.Agent49BoxEncoded.boxes[28]! i := by
  have h : ∀ i : Fin 12, i ≠ 7 →
    codes 0 i = if i = 6 then [14] else BB6.Agent49BoxEncoded.boxes[28]! i := by decide
  by_cases hi : i = 7
  · subst i; rfl
  · rw [if_neg hi, ← h i hi]
    have eq : ∀ (d : Fin 25) (i : Fin 12), i ≠ 7 → codes d i = codes 0 i := by decide
    exact eq d1 i hi

theorem domain_source (d1 : Fin 25) : domain d1 = sourceDomain d1 := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (28 : Fin 34) s
  change raw10Remainder[28]! s =
    (BB6.Agent49BoxEncoded.boxes[28]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  have hi : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
    rcases s with ⟨q,b⟩
    revert q b
    decide
  have hd : decode = BB6.Agent17Raw10BoxFar.decodeCode := by
    funext v
    revert v
    decide
  unfold domain sourceDomain
  rw [codes_match]
  by_cases h7 : index s = 7
  · simp [h7]
  · by_cases h6 : index s = 6
    · simp [h7,h6]
    · simp only [if_neg h7, if_neg h6]
      rw [h,hi,hd]

abbrev ef := swapStates (4 : Fin 6) 5
def eCode (d : Fin 4) : Fin 25 := ⟨17+d.val,by omega⟩
def fCode (d : Fin 4) : Fin 25 := ⟨21+d.val,by omega⟩

theorem ef_row : ∀ (d : Fin 4) (q : Fin 6) (b : Bool) (v : Fin 25),
    v ∈ codes (fCode d) (index (ef.backward q,b)) →
    (decode v).map (renameMove ef) ∈ (codes (eCode d) (index (q,b))).map decode := by decide

theorem ef_fits (d : Fin 4) (m : Machine) (hm : Fits (domain (fCode d)) m) :
    Fits (domain (eCode d)) (renameTable ef m) := by
  intro s
  obtain ⟨q,b⟩ := s
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (hm (ef.backward q,b))
  change (m (ef.backward q,b)).map (renameMove ef) ∈ _
  rw [← he]
  exact ef_row d q b v hv

theorem ef_bound (B : Nat) (d : Fin 4)
    (h : ∀ m, Fits (sourceDomain (eCode d)) m → WeightedBound B m)
    (m : Machine) (hm : Fits (sourceDomain (fCode d)) m) : WeightedBound B m := by
  rw [← domain_source] at hm
  have hA : m (0,false) = decode 8 := by
    have hh := hm (0,false)
    change m (0,false) ∈ [decode 8] at hh
    simpa using hh
  have hz : zeroNext m 0 = none := by rw [zeroNext,hA]; rfl
  apply weighted_rename_back B ef m (by decide) hz
  apply h
  rw [← domain_source]
  exact ef_fits d m hm

theorem parent_fits (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (d1 : Fin 25) (h0 : m (3,false) = decode 14) (h1 : m (3,true) = decode d1) :
    Fits (sourceDomain d1) m := by
  intro s
  unfold sourceDomain
  by_cases h7 : index s = 7
  · rw [if_pos h7]
    have hs : s = slot 7 := by rw [← slot_index s,h7]
    rw [hs]
    change m (3,true) ∈ [decode d1]
    simp [h1]
  · rw [if_neg h7]
    by_cases h6 : index s = 6
    · rw [if_pos h6]
      have hs : s = slot 6 := by rw [← slot_index s,h6]
      rw [hs]
      change m (3,false) ∈ [decode 14]
      simp [h0]
    · rw [if_neg h6]
      exact hm s

def hardCodes : List (Fin 25) := [3,4,17,18,19,20]

theorem classify : ∀ d1 : Fin 25,
    (BB6.Agent17.Box28Simple.secondWitness 14 d1).isSome = true ∨
    d1 ∈ hardCodes ∨ ∃ d : Fin 4, d1 = fCode d := by decide

theorem d14_bound (B : Nat) (hB : 11 ≤ B)
    (h : ∀ d1 ∈ hardCodes, ∀ m, Fits (sourceDomain d1) m → WeightedBound B m)
    (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (3,false) = decode 14) : WeightedBound B m := by
  have e : raw10Remainder[28]! (3,true) = (List.finRange 25).map decode := by decide
  have hh := hm (3,true)
  rw [e] at hh
  obtain ⟨d1,_,he⟩ := List.mem_map.mp hh
  have hf := parent_fits m hm d1 h0 he.symm
  rcases classify d1 with hs | hh | ⟨d,hd⟩
  · have hb := BB6.Agent17.Box28Simple.parent_second m hm 14 d1 h0 he.symm hs
    intro k j hk hj
    exact Nat.le_trans (hb k j hk hj) hB
  · exact h d1 hh m hf
  · subst d1
    exact ef_bound B d (h (eCode d) ((by decide : ∀ d : Fin 4, eCode d ∈ hardCodes) d)) m hf

#print axioms d14_bound
#print axioms domain_source
#print axioms ef_bound
end BB6.Agent17.Box28Orbit

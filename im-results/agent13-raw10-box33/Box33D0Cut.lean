import Box17AuditCore
import Raw10EncodedSourceBridge
import WeightedSymmetry
import Box33GrowthSource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13.Box33D0
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent13.Box17 (index slot index_slot slot_index decode haltBound haltBound_sound tableEq tableEq_sound)
open BB6.Agent49BoxBridge (raw10Remainder)
open BB6Coverage.Agent10ZipAudit
open BB6.Agent16WeightedSymmetry

def allowed : List (Fin 25) := [0,2,3,4,5,6,7,9,10,12,14,16,17,18,19,20,21,22,23,24]
def literalParent (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 2 => [11]
  | 4 => [1]
  | 5 => [13]
  | 6 => allowed
  | _ => List.finRange 25

def parent : Box Slot Transition := fun s => (literalParent (index s)).map decode
theorem literalParent_matches : ∀ i : Fin 12,
    literalParent i = BB6.Agent49BoxEncoded.boxes[33]! i := by decide
theorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by
  revert v
  decide
theorem parentEq : parent = raw10Remainder[33]! := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (33 : Fin 34) s
  change raw10Remainder[33]! s =
    (BB6.Agent49BoxEncoded.boxes[33]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  unfold parent
  rw [h,literalParent_matches,index_source]
  rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]

def codes (d : Fin 25) (i : Fin 12) : List (Fin 25) :=
  if i=6 then [d] else literalParent i
def domain (d : Fin 25) : Box Slot Transition := fun s => (codes d (index s)).map decode
def root (d : Fin 25) : PartialMachine := fun s =>
  match codes d (index s) with
  | [v] => some (decode v)
  | _ => none

theorem root_compatible (d : Fin 25) (m : Machine) (h : Fits (domain d) m) :
    compatible (root d) m := by
  intro s t ht
  unfold root at ht
  cases he : codes d (index s) with
  | nil => simp [he] at ht
  | cons a as =>
    cases as with
    | nil =>
      have hmem := h s
      simp [domain,he] at hmem
      simp [he] at ht
      exact hmem.trans ht
    | cons b bs => simp [he] at ht

theorem source_split (m : Machine) (hm : Fits raw10Remainder[33]! m) :
    ∃ d ∈ allowed, compatible (root d) m := by
  rw [←parentEq] at hm
  have hh := hm (slot 6)
  simp only [parent,index_slot] at hh
  change m (slot 6) ∈ allowed.map decode at hh
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hh
  refine ⟨d,hd,root_compatible d m ?_⟩
  intro s
  by_cases hs : index s = 6
  · have hslot : s = slot 6 := by rw [←slot_index s,hs]
    subst s
    simp [domain,codes,index_slot,he]
  · simpa [domain,codes,hs,parent] using hm s

def closedCodes : List (Fin 25) := [0,5,6,7,9,10]
def retained : List (Fin 25) := [2,3,4,12,14,16,17,18,19,20]
abbrev ef := swapStates (4 : Fin 6) 5
def representative (d : Fin 25) : Fin 25 := Fin.ofNat 25 (d.val-4)

theorem first_partition (d : Fin 25) :
    d ∈ allowed → d ∈ closedCodes ∨ d ∈ retained ∨
      (21 ≤ d.val ∧ representative d ∈ retained) := by
  revert d
  decide

theorem rename_root (d : Fin 25) (h : 21 ≤ d.val) :
    renamePartial ef (root d) = root (representative d) := by
  have hc : ∀ e : Fin 25, 21 ≤ e.val →
      tableEq (renamePartial ef (root e)) (root (representative e)) = true := by decide
  exact tableEq_sound _ _ (hc d h)

inductive Witness where
  | halt (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | growth

def check (p : PartialMachine) : Witness → Bool
  | .halt n => haltBound p n 11
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .growth => tableEq p Box33GrowthSource.p

theorem check_sound (p : PartialMachine) (w : Witness) (h : check p w = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 11 m := by
  cases w with
  | halt n => exact haltBound_sound p n 11 h m hm
  | cycle e k r b =>
    simp only [check,Bool.and_eq_true] at h
    exact weighted_of_never _ _ (zipCycle_sound p e k r b (of_decide_eq_true h.1) h.2 m hm)
  | growth =>
    have he := tableEq_sound _ _ h
    exact weighted_of_never _ _ (Box33GrowthSource.compatible_never m (he ▸ hm))

def firstWitness (d : Fin 25) : Option Witness :=
  match d.val with
  | 0 => some (.halt 3)
  | 5 => some (.cycle 0 6 false (1))
  | 6 => some (.cycle 0 6 false (1))
  | 7 => some (.cycle 0 6 false (1))
  | 9 => some (.cycle 0 5 false (1))
  | 10 => some (.cycle 0 5 false (1))
  | _ => none

def secondSlot (d : Fin 25) : Fin 12 :=
  match d.val with
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 12 => 1
  | 14 => 7
  | 16 => 7
  | 17 => 8
  | 18 => 8
  | 19 => 8
  | 20 => 8
  | _ => 1

def child (d v : Fin 25) : PartialMachine :=
  refine (root d) (slot (secondSlot d)) (decode v)

def secondWitness (d v : Fin 25) : Option Witness :=
  match d.val,v.val with
  | 2, 0 => some (.halt 5)
  | 2, 2 => some (.cycle 0 6 true (-1))
  | 2, 5 => some (.cycle 0 9 false (1))
  | 2, 7 => some (.cycle 0 9 false (1))
  | 2, 9 => some (.cycle 0 8 true (-1))
  | 2, 11 => some (.cycle 2 4 true (-1))
  | 2, 14 => some (.cycle 0 7 true (-1))
  | 2, 16 => some (.cycle 0 7 true (-1))
  | 3, 0 => some (.halt 5)
  | 3, 5 => some (.cycle 0 9 false (1))
  | 3, 7 => some (.cycle 0 9 false (1))
  | 3, 9 => some (.cycle 2 4 false (0))
  | 3, 11 => some (.cycle 2 4 false (0))
  | 4, 0 => some (.halt 5)
  | 4, 2 => some (.cycle 0 6 true (-1))
  | 4, 5 => some (.cycle 0 10 false (1))
  | 4, 7 => some (.cycle 0 10 false (1))
  | 12, 0 => some (.halt 5)
  | 12, 1 => some (.cycle 0 6 false (1))
  | 12, 5 => some (.cycle 0 8 false (1))
  | 12, 6 => some (.cycle 0 8 false (1))
  | 12, 7 => some (.cycle 0 8 false (1))
  | 12, 8 => some (.cycle 1 5 false (1))
  | 12, 9 => some (.cycle 0 7 false (1))
  | 12, 10 => some (.cycle 0 7 false (1))
  | 12, 11 => some (.cycle 0 7 false (1))
  | 12, 12 => some (.cycle 4 2 true (-1))
  | 12, 13 => some (.cycle 3 3 false (0))
  | 14, 0 => some (.halt 5)
  | 14, 1 => some (.cycle 0 6 true (-1))
  | 14, 2 => some (.cycle 0 6 true (-1))
  | 14, 5 => some (.cycle 0 8 false (1))
  | 14, 7 => some (.cycle 0 8 false (1))
  | 14, 8 => some (.cycle 1 5 true (-1))
  | 14, 9 => some (.cycle 0 7 false (1))
  | 14, 10 => some (.cycle 0 7 true (-1))
  | 14, 11 => some (.cycle 0 7 false (1))
  | 14, 13 => some (.cycle 6 1 true (0))
  | 14, 14 => some (.cycle 6 1 true (2))
  | 14, 15 => some (.cycle 4 2 true (0))
  | 14, 16 => some (.cycle 6 1 true (2))
  | 16, 0 => some (.halt 5)
  | 16, 2 => some (.cycle 0 6 true (-1))
  | 16, 9 => some (.cycle 0 9 false (1))
  | 16, 10 => some .growth
  | 16, 11 => some (.cycle 0 9 false (1))
  | 16, 13 => some (.cycle 8 1 true (-2))
  | 16, 14 => some (.cycle 6 1 true (2))
  | 16, 15 => some (.cycle 6 3 false (0))
  | 16, 16 => some (.cycle 6 1 true (2))
  | 17, 0 => some (.halt 4)
  | 17, 1 => some (.cycle 0 5 false (1))
  | 17, 2 => some (.cycle 0 5 false (1))
  | 17, 5 => some (.cycle 0 7 false (1))
  | 17, 6 => some (.cycle 0 7 false (1))
  | 17, 7 => some (.cycle 0 7 false (1))
  | 17, 8 => some (.cycle 1 4 false (1))
  | 17, 9 => some (.cycle 0 6 false (1))
  | 17, 10 => some (.cycle 0 6 false (1))
  | 17, 11 => some (.cycle 0 6 false (1))
  | 17, 13 => some (.cycle 3 2 false (-1))
  | 17, 14 => some (.cycle 3 2 true (-2))
  | 17, 15 => some (.cycle 3 2 false (-1))
  | 17, 17 => some (.cycle 4 1 false (-2))
  | 17, 19 => some (.cycle 4 1 false (-2))
  | 18, 0 => some (.halt 4)
  | 18, 1 => some (.cycle 0 5 false (1))
  | 18, 5 => some (.cycle 0 7 false (1))
  | 18, 7 => some (.cycle 0 7 false (1))
  | 18, 9 => some (.cycle 0 6 false (1))
  | 18, 10 => some (.cycle 0 9 true (-1))
  | 18, 11 => some (.cycle 0 6 false (1))
  | 18, 13 => some (.cycle 3 2 true (-1))
  | 18, 17 => some (.cycle 4 1 false (0))
  | 18, 19 => some (.cycle 4 1 false (0))
  | 19, 0 => some (.halt 4)
  | 19, 1 => some (.cycle 0 5 false (1))
  | 19, 5 => some (.cycle 0 7 false (1))
  | 19, 7 => some (.cycle 0 7 false (1))
  | 19, 9 => some (.cycle 0 6 false (1))
  | 19, 10 => some (.cycle 2 3 false (0))
  | 19, 11 => some (.cycle 0 6 false (1))
  | 19, 13 => some (.cycle 3 2 false (-1))
  | 19, 15 => some (.cycle 3 2 false (-1))
  | 19, 17 => some (.cycle 4 1 false (-2))
  | 19, 19 => some (.cycle 4 1 false (-2))
  | 20, 0 => some (.halt 4)
  | 20, 9 => some (.cycle 2 3 false (0))
  | 20, 11 => some (.cycle 2 3 false (0))
  | _, _ => none

def validateFirst (d : Fin 25) : Bool :=
  match firstWitness d with
  | none => false
  | some w => check (root d) w

def validateSecond (d v : Fin 25) : Bool :=
  match secondWitness d v with
  | none => true
  | some w => check (child d v) w

theorem first_checked : ∀ d : Fin 25, d ∈ closedCodes → validateFirst d = true := by decide
theorem second_checked : ∀ d v : Fin 25, d ∈ retained → validateSecond d v = true := by decide

def remaining (d : Fin 25) : List (Fin 25) :=
  (List.finRange 25).filter fun v => (secondWitness d v).isNone

theorem remaining_count : (retained.map fun d => (remaining d).length).sum = 161 := by decide
theorem decode_complete (t : Transition) : ∃ v : Fin 25, decode v = t := by
  cases t with
  | none => exact ⟨0,rfl⟩
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    revert q w r
    decide

theorem first_bound (d : Fin 25) (hd : d ∈ closedCodes) (m : Machine)
    (hm : compatible (root d) m) : WeightedBound 11 m := by
  have h := first_checked d hd
  cases he : firstWitness d with
  | none => simp [validateFirst,he] at h
  | some w => exact check_sound _ w (by simpa [validateFirst,he] using h) m hm

theorem second_bound (d v : Fin 25) (hd : d ∈ retained) (w : Witness)
    (hw : secondWitness d v = some w) (m : Machine)
    (hm : compatible (child d v) m) : WeightedBound 11 m :=
  check_sound _ w (by simpa [validateSecond,hw] using second_checked d v hd) m hm

theorem raise_bound {B : Nat} (hB : 11 ≤ B) (m : Machine)
    (h : WeightedBound 11 m) : WeightedBound B m := by
  intro k l hk hl
  exact Nat.le_trans (h k l hk hl) hB

/-- Source rectangle 33 reduces to these 161 explicit six-fixed-row cylinders.
    No extra transition choices, including halt, are excluded. The E/F swap
    preserves the weighted bound, not merely ordinary blank-start steps. -/
theorem source_upper (B : Nat) (hB : 11 ≤ B)
    (hOpen : ∀ d ∈ retained, ∀ v ∈ remaining d, ∀ m,
      compatible (child d v) m → WeightedBound B m) :
    ∀ m, Fits raw10Remainder[33]! m → WeightedBound B m := by
  have hret : ∀ d ∈ retained, ∀ m, compatible (root d) m → WeightedBound B m := by
    intro d hd m hm
    obtain ⟨v,hv⟩ := decode_complete (m (slot (secondSlot d)))
    have hc : compatible (child d v) m := by
      unfold child
      rw [hv]
      exact compatible_refine _ m _ hm
    cases he : secondWitness d v with
    | none =>
      have hmem : v ∈ remaining d := by simp [remaining,he]
      exact hOpen d hd v hmem m hc
    | some w => exact raise_bound hB m (second_bound d v hd w he m hc)
  intro m hm
  obtain ⟨d,hd,hc⟩ := source_split m hm
  rcases first_partition d hd with h | h | ⟨h21,hr⟩
  · exact raise_bound hB m (first_bound d h m hc)
  · exact hret d h m hc
  · have he := rename_compatible ef hc
    rw [rename_root d h21] at he
    exact (weightedBound_rename_iff B ef (by decide) m).mp (hret _ hr _ he)

#print axioms remaining_count
#print axioms source_upper
end BB6.Agent13.Box33D0

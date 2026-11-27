import Box28FirstHole

namespace BB6.Agent17.Box28Whole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode index slot)
open BB6.Agent17.Box28Symmetry
open BB6.Agent16WeightedSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def d0Domain : List (Fin 25) := [0,2,3,4,5,6,7,9,10,12,14,16,17,18,19,20,21,22,23,24]
def parentLiteral (i : Fin 12) : List (Fin 25) := if i = 6 then d0Domain else baseLiteral i
def parentDomain : Box Slot Transition := fun s => (parentLiteral (index s)).map decode

theorem parent_matches : ∀ i : Fin 12, parentLiteral i = BB6.Agent49BoxEncoded.boxes[28]! i := by decide

theorem parent_eq : parentDomain = raw10Remainder[28]! := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (28 : Fin 34) s
  change raw10Remainder[28]! s =
    (BB6.Agent49BoxEncoded.boxes[28]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  unfold parentDomain
  rw [h,parent_matches,index_source]
  rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]

theorem ef_parent_mem (q : Fin 6) (r : Bool) (v : Fin 25)
    (h : v ∈ parentLiteral (index (ef.backward q,r))) :
    efCode v ∈ parentLiteral (index (q,r)) := by
  revert q r v
  decide

theorem fits_parent_renamed (m : Machine) (hm : Fits raw10Remainder[28]! m) :
    Fits raw10Remainder[28]! (renameTable ef m) := by
  rw [← parent_eq] at hm ⊢
  intro s
  rcases s with ⟨q,r⟩
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (hm (ef.backward q,r))
  change (m (ef.backward q,r)).map (renameMove ef) ∈ parentDomain (q,r)
  rw [← he,ef_code_decode]
  exact List.mem_map.mpr ⟨efCode v,ef_parent_mem q r v hv,rfl⟩

theorem classify_d0 : ∀ d ∈ d0Domain,
    (Box28Simple.firstWitness d).isSome = true ∨ d = 14 ∨ d = 16 ∨
      d ∈ Box28FirstHole.otherD0 ∨ efCode d ∈ Box28FirstHole.otherD0 := by decide

theorem parent_bound (B : Nat) (hB : 11 ≤ B)
    (h14 : ∀ d ∈ Box28Orbit.hardCodes, ∀ m, Fits (sourceCutFor 14 d) m → WeightedBound B m)
    (h16 : ∀ d ∈ Box28Orbit.hardCodes16, ∀ m, Fits (sourceCutFor 16 d) m → WeightedBound B m)
    (hrest : ∀ d ∈ Box28FirstHole.otherD0, ∀ v ∈ Box28FirstHole.residual d,
      ∀ m, Fits raw10Remainder[28]! m → m (3,false) = decode d →
      m (slot (Box28FirstHole.nextIndex d)) = decode v → WeightedBound B m) :
    ∀ m, Fits raw10Remainder[28]! m → WeightedBound B m := by
  intro m hm
  have hrow := hm (3,false)
  rw [← parent_eq] at hrow
  change m (3,false) ∈ d0Domain.map decode at hrow
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hrow
  rcases classify_d0 d hd with hs | h | h | h | h
  · have hb := Box28Simple.parent_first m hm d he.symm hs
    intro k j hk hj
    exact Nat.le_trans (hb k j hk hj) hB
  · subst d
    exact Box28Orbit.d14_bound B hB h14 m hm he.symm
  · subst d
    exact Box28Orbit.d16_bound B hB h16 m hm he.symm
  · exact Box28FirstHole.d0_bound B hB d (hrest d h) m hm he.symm
  · apply (weightedBound_rename_iff B ef (by decide) m).mp
    apply Box28FirstHole.d0_bound B hB (efCode d) (hrest _ h) _ (fits_parent_renamed m hm)
    change (m (3,false)).map (renameMove ef) = decode (efCode d)
    rw [← he,ef_code_decode]

#print axioms fits_parent_renamed
#print axioms parent_bound
end BB6.Agent17.Box28Whole

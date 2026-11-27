import Box28Whole

namespace BB6.Agent17.Box28Join
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode index slot index_slot)
open BB6.Agent17.Box28Symmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Key := Fin 25 × Fin 25

def second (d : Fin 25) : Fin 12 :=
  if d = 14 ∨ d = 16 then 7 else Box28FirstHole.nextIndex d

def cut (p : Key) : Box Slot Transition := fun s =>
  if index s = second p.1 then [decode p.2] else if index s = 6 then [decode p.1]
  else raw10Remainder[28]! s

def Good (B : Nat) (p : Key) : Prop := ∀ m, Fits (cut p) m → WeightedBound B m

def canonical : List Key :=
  Box28Orbit.hardCodes.map (fun v => (14,v)) ++
  Box28Orbit.hardCodes16.map (fun v => (16,v)) ++
  Box28FirstHole.otherD0.flatMap (fun d => (Box28Whole.normalResidual d).map (fun v => (d,v)))

theorem canonical_count : canonical.length = 118 := by decide
theorem canonical_nodup : canonical.Nodup := by decide

theorem first_slot (d : Fin 25) : second d ≠ 6 := by revert d; decide

theorem fit_cut (d v : Fin 25) (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (slot 6) = decode d) (h1 : m (slot (second d)) = decode v) :
    Fits (cut (d,v)) m := by
  intro s
  unfold cut
  by_cases h7 : index s = second d
  · have hs : s = slot (second d) := by rw [← BB6.Agent13.Box17.slot_index s,h7]
    simp [hs,index_slot,h1]
  · by_cases h6 : index s = 6
    · have hs : s = slot 6 := by rw [← BB6.Agent13.Box17.slot_index s,h6]
      simp [hs,index_slot,first_slot,h0]
    · simpa [h7,h6] using hm s

theorem parent_bound (B : Nat) (hB : 11 ≤ B)
    (h : ∀ p ∈ canonical, Good B p) :
    ∀ m, Fits raw10Remainder[28]! m → WeightedBound B m := by
  apply Box28Whole.parent_bound B hB
  · intro v hv
    exact h (14,v) (by simp [canonical,hv])
  · intro v hv
    exact h (16,v) (by simp [canonical,hv])
  · intro d hd v hv m hm h0 h1
    have hneq : d ≠ 14 ∧ d ≠ 16 := by
      have ht : ∀ x ∈ Box28FirstHole.otherD0, x ≠ 14 ∧ x ≠ 16 := by decide
      exact ht d hd
    have he : second d = Box28FirstHole.nextIndex d := by simp [second,hneq]
    apply h (d,v) ?_ m
    · simp only [canonical,List.mem_append,List.mem_flatMap,List.mem_map]
      exact Or.inr ⟨d,hd,v,hv,rfl⟩
    · exact fit_cut d v m hm h0 (he.symm ▸ h1)

/-- Only the listed, genuinely open cut keys survive this source theorem. -/
theorem parent_bound_residual (B : Nat) (hB : 11 ≤ B)
    (known : List Key) (hk : ∀ p ∈ known, Good B p)
    (hopen : ∀ p ∈ canonical.filter (fun p => !known.contains p), Good B p) :
    ∀ m, Fits raw10Remainder[28]! m → WeightedBound B m := by
  apply parent_bound B hB
  intro p hp
  by_cases h : p ∈ known
  · exact hk p h
  · apply hopen p
    simp [hp,h]

theorem good_mono (B C : Nat) (h : B ≤ C) (p : Key) (hg : Good B p) : Good C p := by
  intro m hm k j hk hj
  exact Nat.le_trans (hg m hm k j hk hj) h

#print axioms parent_bound
#print axioms parent_bound_residual
end BB6.Agent17.Box28Join

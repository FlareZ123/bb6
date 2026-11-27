import Box33D0Cut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box33Residual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent13.Box17 (tableEq tableEq_sound)
open BB6.Agent49BoxBridge (raw10Remainder)
open BB6.Agent16WeightedSymmetry
open Box33D0

/-- The first restriction is invariant under E/F interchange for these six D0 codes. -/
def symmetric (d : Fin 25) : Bool := ([2,3,4,12,14,16] : List (Fin 25)).contains d

def reducedRemaining (d : Fin 25) : List (Fin 25) :=
  (remaining d).filter fun v => !(symmetric d && decide (21 ≤ v.val))

theorem reduced_count : (retained.map fun d => (reducedRemaining d).length).sum = 137 := by decide

theorem representative_mem (d v : Fin 25) (hd : d ∈ retained) (hv : v ∈ remaining d)
    (hs : symmetric d = true) (h21 : 21 ≤ v.val) :
    representative v ∈ reducedRemaining d := by
  have hc : ∀ a b : Fin 25,
      (a ∈ retained ∧ b ∈ remaining a ∧ symmetric a = true ∧ 21 ≤ b.val) →
      representative b ∈ reducedRemaining a := by decide
  exact hc d v ⟨hd,hv,hs,h21⟩

theorem rename_child (d v : Fin 25) (hd : d ∈ retained)
    (hs : symmetric d = true) (h21 : 21 ≤ v.val) :
    renamePartial ef (child d v) = child d (representative v) := by
  have h : ∀ d v : Fin 25, d ∈ retained → symmetric d = true → 21 ≤ v.val →
      tableEq (renamePartial ef (child d v)) (child d (representative v)) = true := by decide
  exact tableEq_sound _ _ (h d v hd hs h21)

theorem source_upper_reduced (B : Nat) (hB : 11 ≤ B)
    (hOpen : ∀ d ∈ retained, ∀ v ∈ reducedRemaining d, ∀ m,
      compatible (child d v) m → WeightedBound B m) :
    ∀ m, Fits raw10Remainder[33]! m → WeightedBound B m := by
  apply source_upper B hB
  intro d hd v hv m hm
  by_cases h : symmetric d = true ∧ 21 ≤ v.val
  · have he := rename_compatible ef hm
    rw [rename_child d v hd h.1 h.2] at he
    exact (weightedBound_rename_iff B ef (by decide) m).mp
      (hOpen d hd _ (representative_mem d v hd hv h.1 h.2) _ he)
  · have hmem : v ∈ reducedRemaining d := by
      simp only [reducedRemaining,List.mem_filter]
      refine ⟨hv,?_⟩
      cases hs : symmetric d
      · simp
      · have hn : ¬ 21 ≤ v.val := fun he => h ⟨hs,he⟩
        simp [hs,hn]
    exact hOpen d hd v hmem m hm

/-- A source theorem roster can discharge the reduced frontier without relying on index order. -/
theorem source_upper_after (B : Nat) (hB : 11 ≤ B) (closed : List (Fin 25 × Fin 25))
    (hClosed : ∀ d v : Fin 25, (d,v) ∈ closed → ∀ m,
      compatible (child d v) m → WeightedBound B m)
    (hOpen : ∀ d ∈ retained, ∀ v ∈ reducedRemaining d, (d,v) ∉ closed → ∀ m,
      compatible (child d v) m → WeightedBound B m) :
    ∀ m, Fits raw10Remainder[33]! m → WeightedBound B m := by
  apply source_upper_reduced B hB
  intro d hd v hv m hm
  by_cases hc : (d,v) ∈ closed
  · exact hClosed d v hc m hm
  · exact hOpen d hd v hv hc m hm

#print axioms reduced_count
#print axioms source_upper_reduced
#print axioms source_upper_after
end BB6.Agent13.Box33Residual

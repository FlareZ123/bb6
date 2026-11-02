import Prune
namespace BB6Coverage

/-- An unused second entry is visibly different from the blank-read slot. -/
def unusedSlot : Slot := (⟨0, by decide⟩, true)

private theorem unusedSlot_unassigned : driftLeaf true unusedSlot = none := by
  simp [driftLeaf, unusedSlot, initialSlot, refine, emptyTable]

/-- Each of the 25 possible assignments to the unreachable A/1 slot
    retains the actual certified A/0=0RA infinite right drift. -/
theorem drift_all_twentyfive_children (B : Nat) (t : Transition) :
    Cover (DecidedBelow B) (refine (driftLeaf true) unusedSlot t) := by
  apply Cover.leaf
  intro m hm
  left
  apply blankDrift_never m true
  exact hm initialSlot (some (blankDrift true)) (by
    simp [refine, driftLeaf, unusedSlot, initialSlot])

/-- A literal, finite 25-way complete branch with 25 proved source-level
    leaves, rather than a generic conditional Cover.sound implication. -/
theorem drift_twentyfive_way_tree (B : Nat) :
    Cover (DecidedBelow B) (driftLeaf true) := by
  apply Cover.branch (driftLeaf true) unusedSlot
  · exact unusedSlot_unassigned
  · intro t ht
    exact drift_all_twentyfive_children B t

#print axioms BB6Coverage.drift_twentyfive_way_tree
end BB6Coverage

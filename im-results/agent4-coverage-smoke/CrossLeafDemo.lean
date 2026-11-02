import CrossSparse
import LeafDemo
import Prune

namespace BB6.CoverageAdapter

theorem imported_rightwalker_same_cylinder :
    sparseTo8 BB6.Coverage.rightWalkerPartial = BB6Coverage.driftLeaf true := by
  funext slot
  rcases slot with ⟨q,b⟩
  by_cases he : q = 0 ∧ b = false
  · rcases he with ⟨hq,hb⟩
    subst q
    subst b
    simp [sparseTo8, BB6.Coverage.rightWalkerPartial, BB6Coverage.driftLeaf,
      BB6Coverage.refine, BB6Coverage.initialSlot, BB6Coverage.blankDrift,
      instructionTo8]
  · simp [sparseTo8, BB6.Coverage.rightWalkerPartial, BB6Coverage.driftLeaf,
      BB6Coverage.refine, BB6Coverage.initialSlot, BB6Coverage.blankDrift,
      instructionTo8, BB6Coverage.emptyTable, he]

theorem imported_original_shift_leaf (B : Nat) :
    BB6Coverage.Cover (BoundedRuntime B) (BB6Coverage.driftLeaf true) := by
  rw [← imported_rightwalker_same_cylinder]
  exact import_source_tree_as_cover_leaf B BB6.Coverage.rightWalkerPartial
    (BB6.Coverage.rightWalkerTree B)

end BB6.CoverageAdapter

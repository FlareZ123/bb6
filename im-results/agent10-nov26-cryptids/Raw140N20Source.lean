import Raw140N20Parent
import Nov26N20

namespace BB6.Agent10Raw140N20
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10Nov26

theorem source_eq : sourceLeaf = leaf n20 := tableOK_sound _ _ (by decide)
theorem cover : Cover (WeightedBound 400) parent := by
  apply cover_of_source
  rw [source_eq]
  exact n20_cover

#print axioms source_eq
#print axioms cover
end BB6.Agent10Raw140N20

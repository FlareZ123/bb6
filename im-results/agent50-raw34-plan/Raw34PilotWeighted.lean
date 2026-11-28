import Raw34Pilot
import WeightedFirstOneCover
namespace BB6.Agent50Raw34Pilot
open BB6Coverage BB6.Agent13BlankDelay
theorem cover_weighted : Cover (WeightedBound 28) parent := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 28 m (cover.sound m hm) (by decide)
#print axioms cover_weighted
end BB6.Agent50Raw34Pilot

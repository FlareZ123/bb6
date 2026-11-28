import Raw43ParentCutExpandedNine
import Raw43B0LEComplete
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43ParentComplete
open BB6Coverage

theorem cover :
    Cover (WeightedBound 11292) BB6.Agent25Raw43Parent.parent :=
  BB6.Agent25Raw43ParentExpandedNine.cover_from_b0le (by decide)
    (BB6.Agent38Raw43B0LEComplete.cover (by decide))

theorem all_completions (m : Machine)
    (hm : compatible BB6.Agent25Raw43Parent.parent m) :
    WeightedBound 11292 m :=
  cover.sound m hm

#print axioms cover
#print axioms all_completions
end BB6.Agent38Raw43ParentComplete

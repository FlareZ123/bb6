import Raw85SiblingData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent21Raw85
open BB6Coverage BB6.Agent13BlankDelay

abbrev parent : PartialMachine := BB6.Agent21Raw85Sibling.sourceParent

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem all_completions : ∀ m, compatible parent m → WeightedBound 7014 m := by
  intro m hm
  apply BB6.Agent21Raw85Sibling.all_completions_weighted m
  rw [BB6.Agent21Raw85Sibling.wideParent_matches_sourceParent]
  exact hm

#print axioms parent_root
#print axioms all_completions
end BB6.Agent21Raw85

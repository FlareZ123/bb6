import Raw73Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent21Raw73
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10Raw73

/-- The literal raw73 cylinder, independently matched against the generated parent. -/
def parent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_matches : p73 = parent :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide)

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem all_completions (m : Machine) (hm : compatible parent m) : WeightedBound 7014 m := by
  apply all73 m
  simpa only [parent_matches] using hm

#print axioms parent_matches
#print axioms all_completions
end BB6.Agent21Raw73

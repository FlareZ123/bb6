import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45FullChild
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay
def parent : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,2⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => none
  | (4,true) => none
  | (5,false) => none
  | (5,true) => none
  | _ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro slot
  rcases slot with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide


end BB6.Agent24Raw45FullChild

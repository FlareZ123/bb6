import Raw45ZipHybrid
import Raw45Depth3FullResidual2
import Raw45Depth3FullResidual11
import Raw45Depth3FullResidual12
import Raw45Depth3FullResidual13
import Raw45Depth3FullResidual14
import Raw45Depth3FullResidual15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Depth2Parent124
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent24Raw45ZipHybrid
namespace R2 := BB6.Agent24Raw45Depth3Full2
namespace R11 := BB6.Agent24Raw45Depth3Full11
namespace R12 := BB6.Agent24Raw45Depth3Full12
namespace R13 := BB6.Agent24Raw45Depth3Full13
namespace R14 := BB6.Agent24Raw45Depth3Full14
namespace R15 := BB6.Agent24Raw45Depth3Full15

/-- Raw45 depth-two residual 124. Five rows A1,C1,E0,F0,F1 remain open. -/
def parent : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => none
  | (4,true) => some (some ⟨false,false,4⟩)
  | (5,false) => none
  | (5,true) => none
  | _ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro slot
  rcases slot with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem cover2_119 : Cover (WeightedBound 119) R2.parent :=
  Cover.leaf _ (by
    intro m hm k d hk hd
    exact Nat.le_trans (R2.all_completions_weighted m hm k d hk hd) (by omega))

theorem cover11_119 : Cover (WeightedBound 119) R11.parent :=
  Cover.leaf _ (by
    intro m hm k d hk hd
    exact Nat.le_trans (R11.all_completions_weighted m hm k d hk hd) (by omega))

/-- E0 is first queried at step 11. Eighteen ordinary E0 moves close by
    translated side cycles; the six remaining moves are complete four-hole
    Covers. This collapses the whole 25^5 physical cylinder at bound 119. -/
def tree : Hybrid 119 :=
  .split 11 (4,false) (byHybridMove [
    .closed (.cycle 0 12 false (3)),
    .closed (.cycle 8 10 false (2)),
    .closed (.cycle 13 1 false (-1)),
    .closed (.cycle 12 1 false (-2)),
    .closed (.cycle 11 1 false (-1)),
    .covered R11.parent cover11_119,
    .closed (.cycle 0 12 true (-1)),
    .closed (.cycle 8 10 true (-1)),
    .closed (.cycle 13 1 false (1)),
    .closed (.cycle 12 1 false (0)),
    .closed (.cycle 11 1 true (-1)),
    .covered R2.parent cover2_119,
    .covered R13.parent R13.cover,
    .covered R12.parent R12.cover,
    .closed (.cycle 1 13 false (3)),
    .closed (.cycle 12 1 false (-2)),
    .closed (.cycle 11 1 false (-1)),
    .covered R14.parent R14.cover,
    .closed (.cycle 7 13 false (3)),
    .closed (.cycle 1 11 false (3)),
    .closed (.cycle 8 9 false (2)),
    .closed (.cycle 11 4 true (-1)),
    .closed (.cycle 11 1 true (-1)),
    .covered R15.parent R15.cover
  ])

theorem checked : check 119 parent tree = true := by decide +kernel

theorem cover : Cover (WeightedBound 119) parent :=
  sound 119 parent tree parent_root parent_nohalt checked

theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 119 m :=
  cover.sound

#print axioms checked
#print axioms cover
#print axioms all_completions_weighted
end BB6.Agent24Raw45Depth2Parent124

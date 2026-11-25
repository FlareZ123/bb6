import Raw39B0RBData
import PartialAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

open BB6.Agent47PartialAudit
def partialKids : Move → PartialAudit := byPartialMove [
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 13 1 false (1)),
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .closed treeChild,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 12 true (0)),
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .unresolved,
  .unresolved]
def partialTree : PartialAudit := .split 6 (0,true) partialKids
theorem partialKids_checked (mv : Move) :
    partialCheck 1271 (refine p39 (0,true) (some mv)) (partialKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact treeChild_checked
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
theorem partialTree_checked : partialCheck 1271 p39 partialTree = true := by
  change (zipQueryOK 1271 p39 6 (0,true) && allMoves (fun mv => partialCheck 1271 (refine p39 (0,true) (some mv)) (partialKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query39,allMoves_of _ partialKids_checked⟩
def residuals := partialResiduals p39 partialTree
theorem residual_count : residuals.length = 14 := by decide
theorem cut_sound : ∀ m, compatible p39 m →
    WeightedBound 1271 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 1271 p39 partialTree p39_root p39_nohalt partialTree_checked
#print axioms cut_sound
#print axioms residual_count

end BB6.Agent11Raw39B0RB

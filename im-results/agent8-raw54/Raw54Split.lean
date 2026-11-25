import Raw54Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def e1Kids : Move → PartialAudit := byPartialMove [
.closed (.cycle 0 8 false (3)),
.closed (.cycle 7 6 false (0)),
.closed (.cycle 9 1 false (-1)),
.closed (.cycle 8 1 false (-2)),
.closed (.cycle 7 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 9 1 false (1)),
.closed (.cycle 8 1 false (0)),
.closed (.cycle 14 1 true (2)),
.unresolved,
.unresolved,
tree,
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 8 1 false (-2)),
.closed (.cycle 7 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 31 18 false (0)),
.closed (.cycle 7 3 false (0)),
.closed (.cycle 25 1 true (-3)),
.unresolved]
theorem e1Kids_checked (mv : Move) :
    partialCheck 7014 (refine e1 (4,false) (some mv)) (e1Kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact checked
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

def e1Tree : PartialAudit := .split 7 (4,false) e1Kids
theorem e1_checked : partialCheck 7014 e1 e1Tree = true := by
  change (zipQueryOK 7014 e1 7 (4,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014 (refine e1 (4,false) (some mv)) (e1Kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨e1_query, allMoves_of _ e1Kids_checked⟩

theorem raw54_nohalt : weightedTNFNoAssignedHalt raw54 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
theorem e1_nohalt : weightedTNFNoAssignedHalt e1 :=
  weightedTNFNoAssignedHalt_refine _ _ _ raw54_nohalt
theorem e1_root : e1 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem e1_sound : ∀ m, compatible e1 m → WeightedBound 7014 m ∨
    ∃ e ∈ partialResiduals e1 e1Tree, compatible e.2 m :=
  partialSound 7014 e1 e1Tree e1_root e1_nohalt e1_checked
#print axioms e1_sound
end BB6.Agent8Raw54

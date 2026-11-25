import Raw38Pump
import PartialAudit
import TNFPilot
import RosterCoverComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw38Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,false,0⟩)

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)

def c1Kids : Move → PartialAudit := byPartialMove [
  .closed (.cycle 6 15 true 0),
  .unresolved,
  .closed (.cycle 15 1 false 1),
  .closed (.cycle 15 1 false 3),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 12 true 0),
  .unresolved,
  .closed (.proven BB6Coverage.Agent19Raw38Pump.table BB6Coverage.Agent19Raw38Pump.never),
  .closed (.cycle 3 9 true 0),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 7 7 false 3),
  .closed (.cycle 0 16 true 0),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 12 true 0),
  .closed (.cycle 1 11 true 0),
  .closed (.cycle 2 10 true 0),
  .closed (.cycle 0 17 true 0),
  .unresolved,
  .unresolved]

def tree : PartialAudit := .split 6 (0,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false 0),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .split 11 (2,true) c1Kids,
  .closed (.cycle 7 1 false 1),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

theorem checked : partialCheck 395 parent tree = true := by decide

def residuals := partialResiduals parent tree

theorem residual_count : residuals.length = 31 := by decide

theorem cut_sound : ∀ m, compatible parent m →
    WeightedBound 395 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 395 parent tree parent_root parent_nohalt checked

theorem parent_cover {B : Nat} (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ residuals, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) parent := by
  refine .leaf _ ?_
  intro m hm
  rcases cut_sound m hm with hb | ⟨e,he,hc⟩
  · exact BB6.Agent13RosterComposition.weightedBound_mono_local hB hb
  · exact (hLeaves e he).sound m hc

#print axioms checked
#print axioms cut_sound
#print axioms parent_cover
end BB6.Agent19Raw38Cut

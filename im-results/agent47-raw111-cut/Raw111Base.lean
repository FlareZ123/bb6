import PartialAudit
import ZipPrefixAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw111
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

/-- Canonical retained raw111, E1=0RC, first hole C1 at time 7. -/
abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,2⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev child (mv : Move) : PartialMachine := refine parent (2,true) (some mv)

def shallowKids : Move → PartialAudit := byPartialMove [
  .closed (.cycle 0 8 true 0), .closed (.cycle 1 7 true 1),
  .closed (.cycle 2 6 true 1), .unresolved, .unresolved, .unresolved,
  .closed (.cycle 0 8 true 0), .closed (.cycle 1 7 true 1),
  .closed (.far false 1 ⟨0,[0,0],[2,4,8,4,64,64,64],[64,64,4,16,4,64,64],112⟩),
  .unresolved, .unresolved, .unresolved, .unresolved, .unresolved, .unresolved,
  .closed (.cycle 4 4 true 1), .unresolved, .unresolved,
  .closed (.cycle 0 8 true 0), .closed (.cycle 1 7 true 1),
  .closed (.cycle 2 6 true 1), .unresolved, .unresolved, .unresolved]

def shallow : PartialAudit := .split 7 (2,true) shallowKids
theorem shallow_checked : partialCheck 7014 parent shallow = true := by decide
def shallowResiduals := partialResiduals parent shallow
theorem shallow_count : shallowResiduals.length = 14 := by decide
theorem shallow_sound :
    ∀ m, compatible parent m → WeightedBound 7014 m ∨
      ∃ e ∈ shallowResiduals, compatible e.2 m :=
  partialSound 7014 parent shallow parent_root parent_nohalt shallow_checked

#print axioms shallow_sound
end BB6.Agent47Raw111

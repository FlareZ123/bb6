import Raw10BoxBridge
import Raw10FixedLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10Box0Halt
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109

/-- The identical four-slot two-move halt cylinder. -/
abbrev haltTable : PartialMachine := BB6.Agent13Raw10FixedLeaves.haltTable

def witness : Machine := fun slot => (haltTable slot).getD none

theorem halts (m : Machine) (hm : compatible haltTable m) :
    HaltsAfter m 2 :=
  BB6.Agent13Raw10FixedLeaves.halt_exact m hm

theorem root : haltTable initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent13Raw10FixedLeaves.halt_root

theorem exactly_four_assigned :
    ∀ s, haltTable s ≠ none ↔
      s = (0,false) ∨ s = (0,true) ∨ s = (1,false) ∨ s = (2,true) :=
  BB6.Agent13Raw10FixedLeaves.exactly_four_assigned

theorem delay_bound :
    ∀ d ∈ possibleDelays haltTable 0, d + 2 + 1 ≤ 7014 := by
  intro d hd
  exact Nat.le_trans (BB6.Agent13Raw10FixedLeaves.halt_delay_bound d hd) (by decide)

def cover : Cover (WeightedBound 7014) haltTable :=
  weighted_halt_leaf haltTable 7014 2 root halts delay_bound

theorem table_refines_parent :
    ∀ s t, firstOneB0_1LC s = some t → haltTable s = some t := by
  intro s t hs
  have href : refinesMachine haltTable firstOneB0_1LC :=
    refinesMachineB_sound (by decide)
  rcases href s with hn | he
  · rw [hs] at hn
    contradiction
  · exact he.trans hs

theorem compatible_parent (m : Machine) (hm : compatible haltTable m) :
    compatible firstOneB0_1LC m := by
  intro s t hs
  exact hm s t (table_refines_parent s t hs)

#print axioms halts
#print axioms delay_bound
#print axioms cover
#print axioms compatible_parent
end BB6.Agent50Raw10Box0Halt

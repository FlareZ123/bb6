import Raw10BoxBridge
import Raw10FixedLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10Box8
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent49BoxBridge
open BB6.Agent47Canonical78

/-- The identical ten-slot lasso cylinder, proved via the accepted sparse
    zipper checker rather than symbolic tape simplification. -/
abbrev table : PartialMachine := BB6.Agent13Raw10FixedLeaves.cycleTable

def witness : Machine := fun slot => (table slot).getD none

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent13Raw10FixedLeaves.cycle_never m hm

theorem holes_exact : ∀ s, table s = none ↔ s = (1,true) ∨ s = (5,true) :=
  BB6.Agent13Raw10FixedLeaves.holes_exact

theorem root : table initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent13Raw10FixedLeaves.cycle_root

theorem support : TNFSupport table 6 :=
  BB6.Agent13Raw10FixedLeaves.support

theorem no_assigned_halt : weightedTNFNoAssignedHalt table :=
  BB6.Agent13Raw10FixedLeaves.no_assigned_halt

def certificate (B : Nat) : WeightedTNFCertificate B table 6 :=
  BB6.Agent13Raw10FixedLeaves.certificate B

def cover (B : Nat) : Cover (WeightedBound B) table :=
  (certificate B).toCover

theorem table_refines_parent :
    ∀ s t, firstOneB0_1LC s = some t → table s = some t := by
  intro s t hs
  have href : refinesMachine table firstOneB0_1LC :=
    refinesMachineB_sound (by decide)
  rcases href s with hn | he
  · rw [hs] at hn
    contradiction
  · exact he.trans hs

theorem compatible_parent (m : Machine) (hm : compatible table m) :
    compatible firstOneB0_1LC m := by
  intro s t hs
  exact hm s t (table_refines_parent s t hs)

#print axioms never
#print axioms certificate
#print axioms cover
#print axioms compatible_parent
end BB6.Agent50Raw10Box8

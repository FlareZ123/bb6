import F412Depth7BoxGraft
import F412Depth6TwoReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth6TwoBox
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft
open BB6.Agent26F412Depth7Box BB6.Agent26F412Depth6Two
open BB6.Agent49Box BB6.Agent49BoxBridge BB6.Agent17Raw10CombinedConsumer

/-- Both depth-six parents as actual partial transition tables. -/
def fDepth6TwoTables : List PartialMachine :=
  fDepth6Two.map fun e => fChild e.1 e.2

theorem fDepth6TwoTables_sound (B : Nat) (hB : 128 ≤ B)
    (p : PartialMachine) (hp : p ∈ fDepth6TwoTables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
  exact fDepth6Two_sound B hB e he m hm

/-- Live raw10-box frontier after all 91 disjoint F412 cuts. -/
def fShort91Tables : List PartialMachine := fShort89Tables ++ fDepth6TwoTables
theorem fShort91Tables_length : fShort91Tables.length = 91 := by decide

theorem fShort91Tables_sound (B : Nat) (hB : 128 ≤ B)
    (p : PartialMachine) (hp : p ∈ fShort91Tables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hp with hl | hr
  · exact fShort89Tables_sound B hB p hl m hm
  · exact fDepth6TwoTables_sound B hB p hr m hm

def raw10Short91Remainder : List (Box Slot Transition) :=
  graftBoxes raw10RemainderWithCycleAndHalt fShort91Tables

theorem raw10Short91Remainder_exact (m : Machine) :
    (∃ r ∈ raw10Short91Remainder, Fits r m) ↔
      (∃ r ∈ raw10RemainderWithCycleAndHalt, Fits r m) ∧
      ∀ p ∈ fShort91Tables, ¬ compatible p m :=
  graftBoxes_exact _ _ m

theorem raw10Short91Remainder_disjoint :
    raw10Short91Remainder.Pairwise Disjoint :=
  graftBoxes_disjoint _ _ raw10RemainderWithCycleAndHalt_disjoint

def raw10CoverWithF412Short91 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10Short91Remainder,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent50RootFrontier.firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B hB hHeld
    (graftBoxes_consume B _ _ (fShort91Tables_sound B (by omega)) hOpen)

#print axioms fShort91Tables_sound
#print axioms raw10Short91Remainder_exact
#print axioms raw10CoverWithF412Short91

end BB6.Agent26F412Depth6TwoBox

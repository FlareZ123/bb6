import F412Depth8BoxGraft
import F412Depth7Reduction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth7Box
open BB6Coverage BB6.Agent26F412Graft
open BB6.Agent26F412NewBox BB6.Agent26F412Depth7
open BB6.Agent49Box BB6.Agent49BoxBridge BB6.Agent17Raw10CombinedConsumer

/-- Exactly the thirteen newly closed F0 cylinders. -/
def fDepth7Tables : List PartialMachine :=
  fDepth7Siblings.map fun e => fChild e.1 e.2

theorem fDepth7Tables_length : fDepth7Tables.length = 13 := by decide
theorem fDepth7Tables_sound (B : Nat) (hB : 128 ≤ B)
    (p : PartialMachine) (hp : p ∈ fDepth7Tables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
  exact fDepth7Siblings_weighted B hB e he m hm

/-- All 59 prior side cycles, 9 prior early halters, 4 new nonhalters,
    4 new final-hole leaves, and 13 complete F0 parents. -/
def fShort89Tables : List PartialMachine := fShort76Tables ++ fDepth7Tables

theorem fShort89Tables_length : fShort89Tables.length = 89 := by decide

theorem fShort89Tables_sound (B : Nat) (hB : 128 ≤ B)
    (p : PartialMachine) (hp : p ∈ fShort89Tables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hp with hl | hr
  · exact fShort76Tables_sound B (by omega) p hl m hm
  · exact fDepth7Tables_sound B hB p hr m hm

/-- A genuine live box complement after consuming new 13 F0 cylinders. -/
def raw10Short89Remainder : List (Box Slot Transition) :=
  graftBoxes raw10RemainderWithCycleAndHalt fShort89Tables

theorem raw10Short89Remainder_exact (m : Machine) :
    (∃ r ∈ raw10Short89Remainder, Fits r m) ↔
      (∃ r ∈ raw10RemainderWithCycleAndHalt, Fits r m) ∧
      ∀ p ∈ fShort89Tables, ¬ compatible p m :=
  graftBoxes_exact _ _ m

theorem raw10Short89Remainder_disjoint :
    raw10Short89Remainder.Pairwise Disjoint :=
  graftBoxes_disjoint _ _ raw10RemainderWithCycleAndHalt_disjoint

/-- Improved raw10 cover interface independent of the exact F412 clock. -/
def raw10CoverWithF412Short89 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10Short89Remainder,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent50RootFrontier.firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B hB hHeld
    (graftBoxes_consume B _ _ (fShort89Tables_sound B (by omega)) hOpen)

#print axioms fShort89Tables_sound
#print axioms raw10Short89Remainder_exact
#print axioms raw10CoverWithF412Short89

end BB6.Agent26F412Depth7Box

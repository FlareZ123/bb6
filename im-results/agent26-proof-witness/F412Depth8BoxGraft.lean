import F412BoxGraft
import F412Depth8Reduction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412NewBox
open BB6Coverage BB6.Agent26F412Graft
open BB6.Agent26F412NGram BB6.Agent26F412Depth8 BB6.Agent26F412DeepHalt
open BB6.Agent49Box BB6.Agent49BoxBridge BB6.Agent17Raw10CombinedConsumer

/-- Actual new machine cylinders, not abstract options: four new
    no-halt N-gram branches and four fully bounded last-hole branches. -/
def fEightTables : List PartialMachine :=
  fNewNGram.map (fun e => fChild e.1 e.2) ++
  fDepth8Halt.map (fun e => fChild e.1 e.2)

theorem fEightTables_length : fEightTables.length = 8 := by decide

theorem fEightTables_sound (B : Nat) (hB : 37 ≤ B)
    (p : PartialMachine) (hp : p ∈ fEightTables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hp with hn | hh
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    exact fNewNGram_weighted B e he m hm
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hh
    exact fDepth8Halt_weighted B hB e he m hm

/-- Original 59 certified side nonhalters and nine early halt leaves,
    enlarged by eight new branches, all independent of the long clock. -/
def fShort76Tables : List PartialMachine := fShortTables ++ fEightTables

theorem fShort76Tables_sound (B : Nat) (hB : 37 ≤ B)
    (p : PartialMachine) (hp : p ∈ fShort76Tables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hp with h0 | h8
  · exact fShortTables_sound B (by omega) p h0 m hm
  · exact fEightTables_sound B hB p h8 m hm

/-- Exact live complement in the ongoing raw10 rectangle partition. -/
def raw10Short76Remainder : List (Box Slot Transition) :=
  graftBoxes raw10RemainderWithCycleAndHalt fShort76Tables

theorem raw10Short76Remainder_exact (m : Machine) :
    (∃ r ∈ raw10Short76Remainder, Fits r m) ↔
      (∃ r ∈ raw10RemainderWithCycleAndHalt, Fits r m) ∧
      ∀ p ∈ fShort76Tables, ¬ compatible p m :=
  graftBoxes_exact _ _ m

theorem raw10Short76Remainder_disjoint :
    raw10Short76Remainder.Pairwise Disjoint :=
  graftBoxes_disjoint _ _ raw10RemainderWithCycleAndHalt_disjoint

/-- Global raw10 parent cover reduces to this strictly smaller live
    rectangle complement and the pre-existing held-family premise. -/
def raw10CoverWithF412Short76 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10Short76Remainder,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent50RootFrontier.firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B hB hHeld
    (graftBoxes_consume B _ _ (fShort76Tables_sound B (by omega)) hOpen)

#print axioms fEightTables_length
#print axioms fEightTables_sound
#print axioms raw10Short76Remainder_exact
#print axioms raw10CoverWithF412Short76

end BB6.Agent26F412NewBox

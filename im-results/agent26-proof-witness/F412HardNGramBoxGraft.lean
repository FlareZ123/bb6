import F412HardNGramFour
import F412BoxGraft
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent26F412HardNGramBox
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft
open BB6.Agent26F412HardNGram
open BB6.Agent49Box BB6.Agent49BoxBridge BB6.Agent17Raw10CombinedConsumer
def hardTables : List PartialMachine := [p0,p1,p2,p3]
theorem hardTables_length : hardTables.length = 4 := by decide
theorem hardTables_sound (B : Nat) (p : PartialMachine) (hp : p ∈ hardTables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  have hc : p = p0 ∨ p = p1 ∨ p = p2 ∨ p = p3 := by
    simpa [hardTables] using hp
  rcases hc with h | h | h | h
  · subst p; exact weighted_never B m (never0 m hm)
  · subst p; exact weighted_never B m (never1 m hm)
  · subst p; exact weighted_never B m (never2 m hm)
  · subst p; exact weighted_never B m (never3 m hm)
def raw10HardRemainder : List (Box Slot Transition) :=
  graftBoxes raw10RemainderWithCycleAndHalt hardTables
theorem raw10HardRemainder_exact (m : Machine) :
    (∃ r ∈ raw10HardRemainder, Fits r m) ↔
      (∃ r ∈ raw10RemainderWithCycleAndHalt, Fits r m) ∧
      ∀ p ∈ hardTables, ¬ compatible p m :=
  graftBoxes_exact _ _ m
theorem raw10HardRemainder_disjoint :
    raw10HardRemainder.Pairwise Disjoint :=
  graftBoxes_disjoint _ _ raw10RemainderWithCycleAndHalt_disjoint
def raw10CoverWithHardNGrams (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10HardRemainder,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent50RootFrontier.firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B hB hHeld
    (graftBoxes_consume B _ _ (hardTables_sound B) hOpen)
#print axioms hardTables_sound
#print axioms raw10HardRemainder_exact
#print axioms raw10CoverWithHardNGrams
end BB6.Agent26F412HardNGramBox

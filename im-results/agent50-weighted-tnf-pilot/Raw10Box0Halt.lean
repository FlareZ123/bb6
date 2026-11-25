import Raw10BoxBridge
import Mathlib.Tactic
import WeightedFirstOneCover
import LeafRules

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10Box0Halt
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109

/-- A four-slot subcylinder of the first raw10 residual rectangle.
    A1 and C1 are assigned halt transitions; the other eight slots are free. -/
def haltTable : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (0,true) then some none
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (2,true) then some none
  else none

def witness : Machine := fun slot => (haltTable slot).getD none

private theorem compatible_witness : compatible haltTable witness := by
  intro slot t ht
  simp [witness]
  rw [ht]
  rfl

/-- After A0=1RB and B0=1LC, state C scans the 1 written at cell zero;
    cell one is also 1. -/
def entry : Config :=
  { state := 2, head := 0, tape := fun x => x = 0 ∨ x = 1 }

private theorem entry_run : run witness 2 blank = some entry := by
  simp [run, rawStep, readSlot, blank, applyMove, witness, haltTable, entry]
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [entry, h0, h1]

private theorem halt_run : run witness 3 blank = none := by
  simp [run, rawStep, readSlot, blank, applyMove, witness, haltTable, entry]

/-- The three consulted slots A0, B0, C1 are all assigned, including the
    terminal halt query. -/
private theorem known_prefix :
    ∀ i, i < 3 → ∀ x, run witness i blank = some x →
      haltTable (readSlot x) = some (witness (readSlot x)) := by
  intro i hi x hx
  interval_cases i
  all_goals
    simp [run, rawStep, readSlot, blank, applyMove, witness, haltTable] at hx
    subst x
    simp [haltTable, witness, readSlot]

private theorem known_prefix2 :
    ∀ i, i < 2 → ∀ x, run witness i blank = some x →
      haltTable (readSlot x) = some (witness (readSlot x)) := by
  intro i hi x hx
  exact known_prefix i (by omega) x hx

/-- Every completion of this table executes exactly two ordinary moves and
    then queries the assigned halt at C1. -/
theorem halts (m : Machine) (hm : compatible haltTable m) :
    HaltsAfter m 2 := by
  have h2 : run m 2 blank = some entry := by
    rw [← common_prefix_of_partial_table haltTable witness m blank 2
      compatible_witness hm known_prefix2]
    exact entry_run
  have h3 : run m 3 blank = none := by
    rw [← common_prefix_of_partial_table haltTable witness m blank 3
      compatible_witness hm known_prefix]
    exact halt_run
  unfold HaltsAfter
  rw [h2, h3]
  simp

theorem root :
    haltTable initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem exactly_four_assigned :
    ∀ s, haltTable s ≠ none ↔
      s = (0,false) ∨ s = (0,true) ∨ s = (1,false) ∨ s = (2,true) := by
  decide

/-- The delay correction is bounded by the six possible initial states. -/
theorem delay_bound :
    ∀ d ∈ possibleDelays haltTable 0, d + 2 + 1 ≤ 7014 := by
  intro d hd
  have hmem : d ∈ List.range 6 := (List.mem_filter.mp hd).1
  have hlt : d < 6 := List.mem_range.mp hmem
  omega

/-- The 152,587,890,625-machine halting cylinder is a weighted score-7014
    leaf. -/
def cover : Cover (WeightedBound 7014) haltTable :=
  weighted_halt_leaf haltTable 7014 2 root halts delay_bound

theorem table_refines_parent :
    ∀ s t, firstOneB0_1LC s = some t → haltTable s = some t := by
  decide

theorem compatible_parent (m : Machine) (hm : compatible haltTable m) :
    compatible firstOneB0_1LC m := by
  intro s t hs
  exact hm s t (table_refines_parent s t hs)

#print axioms entry_run
#print axioms halt_run
#print axioms known_prefix
#print axioms halts
#print axioms delay_bound
#print axioms cover
#print axioms compatible_parent
end BB6.Agent50Raw10Box0Halt

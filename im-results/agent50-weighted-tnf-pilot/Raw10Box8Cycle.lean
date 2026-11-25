import Raw10BoxBridge
import Mathlib.Tactic
import LeafRules

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10Box8
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent49BoxBridge
open BB6.Agent47Canonical78

/-- The ten transition slots used by the exact 24+14 lasso. B1 and F1
    remain unassigned. In Raw10Encoded's 0=wildcard convention this is
    [8,14,11,0,17,4,9,2,23,15,10,0]. -/
def table : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (0,true) then some (some ⟨false,true,3⟩)
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (1,true) then none
  else if s = (2,false) then some (some ⟨false,false,4⟩)
  else if s = (2,true) then some (some ⟨true,true,0⟩)
  else if s = (3,false) then some (some ⟨false,false,2⟩)
  else if s = (3,true) then some (some ⟨false,true,0⟩)
  else if s = (4,false) then some (some ⟨true,false,5⟩)
  else if s = (4,true) then some (some ⟨true,false,3⟩)
  else if s = (5,false) then some (some ⟨false,true,2⟩)
  else none

def witness : Machine := fun slot => (table slot).getD none

private theorem compatible_witness : compatible table witness := by
  intro slot t ht
  simp [witness]
  rw [ht]
  rfl

/-- After 24 moves the machine is in D at head zero, with ones at
    -3, -2, and 1, and blank elsewhere. -/
def entry : Config :=
  { state := 3, head := 0, tape := fun x => x = -3 ∨ x = -2 ∨ x = 1 }

private theorem entry_run : run witness 24 blank = some entry := by
  simp [run, rawStep, readSlot, blank, applyMove, witness, table, entry]
  funext x
  by_cases h1 : x = -3 <;> by_cases h2 : x = -2 <;>
    by_cases h3 : x = 1 <;> simp [entry, h1, h2, h3]

/-- Fourteen further moves return to the identical state, head, and
    bi-infinite tape. The seven left and seven right moves cancel. -/
private theorem cycle_run : run witness 14 entry = some entry := by
  simp [run, rawStep, readSlot, applyMove, witness, table, entry]
  funext x
  by_cases h1 : x = -3 <;> by_cases h2 : x = -2 <;>
    by_cases h3 : x = 1 <;> simp [entry, h1, h2, h3]

/-- Every consultation in the 38-step blank-origin lasso is assigned. -/
private theorem known_trace :
    ∀ i, i < 38 → ∀ x, run witness i blank = some x →
      table (readSlot x) = some (witness (readSlot x)) := by
  intro i hi x hx
  interval_cases i
  all_goals
    simp [run, rawStep, readSlot, blank, applyMove, witness, table] at hx
    subst x
    simp [table, witness, readSlot]

private theorem known_entry :
    ∀ i, i < 24 → ∀ x, run witness i blank = some x →
      table (readSlot x) = some (witness (readSlot x)) := by
  intro i hi x hx
  exact known_trace i (by omega) x hx

private theorem known_cycle :
    ∀ i, i < 14 → ∀ x, run witness i entry = some x →
      table (readSlot x) = some (witness (readSlot x)) := by
  intro i hi x hx
  have hfull : run witness (24+i) blank = some x := by
    rw [run_add witness blank 24 i, entry_run]
    exact hx
  exact known_trace (24+i) (by omega) x hfull

/-- The exact lasso transfers to every completion because neither hole
    (B1 nor F1) is consulted in the entry prefix or return cycle. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have hentry : run m 24 blank = some entry := by
    rw [← common_prefix_of_partial_table table witness m blank 24
      compatible_witness hm known_entry]
    exact entry_run
  have hcycle : run m 14 entry = some entry := by
    rw [← common_prefix_of_partial_table table witness m entry 14
      compatible_witness hm known_cycle]
    exact cycle_run
  exact eventually_cycle_never m entry 24 14 (by decide) hentry hcycle

theorem holes_exact :
    ∀ s, table s = none ↔ s = (1,true) ∨ s = (5,true) := by
  decide

theorem root : table initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem support : TNFSupport table 6 := by
  intro s t hs
  exact ⟨s.1.isLt, fun mv hm => mv.next.isLt⟩

theorem no_assigned_halt : weightedTNFNoAssignedHalt table := by
  decide

/-- A proof-carrying score-B TNF leaf for all 625 B1/F1 completions. -/
def certificate (B : Nat) : WeightedTNFCertificate B table 6 :=
  .nonhalt root support no_assigned_halt never

def cover (B : Nat) : Cover (WeightedBound B) table :=
  (certificate B).toCover

theorem table_refines_parent :
    ∀ s t, firstOneB0_1LC s = some t → table s = some t := by
  decide

theorem compatible_parent (m : Machine) (hm : compatible table m) :
    compatible firstOneB0_1LC m := by
  intro s t hs
  exact hm s t (table_refines_parent s t hs)

#print axioms entry_run
#print axioms cycle_run
#print axioms known_trace
#print axioms never
#print axioms certificate
#print axioms cover
#print axioms compatible_parent
end BB6.Agent50Raw10Box8

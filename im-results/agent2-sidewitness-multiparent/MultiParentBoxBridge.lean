import Raw10BoxBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2MultiParentSideWitness

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50RootFrontier
open BB6.Agent47SevenSideWitnesses
open BB6.Agent49Box

/-- Three additional exact first-one residuals in canonical-124. -/
def raw8Parent : PartialMachine :=
  BB6Coverage.refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨false, false, ⟨2, by decide⟩⟩)

def raw9Parent : PartialMachine :=
  BB6Coverage.refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨false, true, ⟨2, by decide⟩⟩)

def raw23B0Parent : PartialMachine :=
  BB6Coverage.refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨true, true, ⟨2, by decide⟩⟩)

def raw23Parent : PartialMachine :=
  BB6Coverage.refine raw23B0Parent
    (⟨2, by decide⟩, false)
    (some ⟨false, false, ⟨3, by decide⟩⟩)

/-- These parents survive the 15 accepted whole-cylinder cuts in the raw 109 roster. -/
theorem raw8_not_covered_109 :
    BB6.Agent47Combined109.covered raw8Parent = false := by decide

theorem raw9_not_covered_109 :
    BB6.Agent47Combined109.covered raw9Parent = false := by decide

theorem raw23_not_covered_109 :
    BB6.Agent47Combined109.covered raw23Parent = false := by decide

theorem raw8_in_reduced109_sameTable :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 raw8Parent = true := by decide

theorem raw9_in_reduced109_sameTable :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 raw9Parent = true := by decide

theorem raw23_in_reduced109_sameTable :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 raw23Parent = true := by decide

theorem raw8_in_reduced109 :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster, e.2 = raw8Parent := by
  obtain ⟨e, he, hs⟩ := raw8_in_reduced109_sameTable
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hs⟩

theorem raw9_in_reduced109 :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster, e.2 = raw9Parent := by
  obtain ⟨e, he, hs⟩ := raw9_in_reduced109_sameTable
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hs⟩

theorem raw23_in_reduced109 :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster, e.2 = raw23Parent := by
  obtain ⟨e, he, hs⟩ := raw23_in_reduced109_sameTable
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hs⟩

/-- These same three parents survive canonical state-introduction filtering
    and the eighteen already accepted 7014-bound cuts in the 78-way roster. -/
theorem raw8_not_covered_106 :
    BB6.Agent47Combined106.covered raw8Parent = false := by decide

theorem raw9_not_covered_106 :
    BB6.Agent47Combined106.covered raw9Parent = false := by decide

theorem raw23_not_covered_106 :
    BB6.Agent47Combined106.covered raw23Parent = false := by decide

theorem raw8_in_canonical78_sameTable :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 raw8Parent = true := by decide

theorem raw9_in_canonical78_sameTable :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 raw9Parent = true := by decide

theorem raw23_in_canonical78_sameTable :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 raw23Parent = true := by decide

theorem raw8_in_canonical78 :
    ∃ e ∈ BB6.Agent47Canonical78.roster, e.2 = raw8Parent := by
  obtain ⟨e, he, hs⟩ := raw8_in_canonical78_sameTable
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hs⟩

theorem raw9_in_canonical78 :
    ∃ e ∈ BB6.Agent47Canonical78.roster, e.2 = raw9Parent := by
  obtain ⟨e, he, hs⟩ := raw9_in_canonical78_sameTable
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hs⟩

theorem raw23_in_canonical78 :
    ∃ e ∈ BB6.Agent47Canonical78.roster, e.2 = raw23Parent := by
  obtain ⟨e, he, hs⟩ := raw23_in_canonical78_sameTable
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hs⟩

/-- The same finite refinement predicate used by the raw10 pilot. -/
def refinesB (child parent : PartialMachine) : Bool :=
  (List.finRange 6).all fun q =>
    [false, true].all fun b =>
      decide (parent (q,b) = none ∨ child (q,b) = parent (q,b))

def raw8SideWitnesses : List SideWitness :=
  witnesses.filter fun w =>
    refinesB (BB6Coverage.unpackTable w.table) raw8Parent

def raw9SideWitnesses : List SideWitness :=
  witnesses.filter fun w =>
    refinesB (BB6Coverage.unpackTable w.table) raw9Parent

def raw23SideWitnesses : List SideWitness :=
  witnesses.filter fun w =>
    refinesB (BB6Coverage.unpackTable w.table) raw23Parent

theorem raw8SideWitnesses_count : raw8SideWitnesses.length = 68 := by decide
theorem raw9SideWitnesses_count : raw9SideWitnesses.length = 108 := by decide
theorem raw23SideWitnesses_count : raw23SideWitnesses.length = 96 := by decide

theorem sideWitnesses_safe (ws : List SideWitness)
    (h : ∀ w ∈ ws, ∀ m,
      BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m →
      WeightedBound 7014 m) :
    ∀ w ∈ ws, ∀ m,
      BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m →
      WeightedBound 7014 m := h

theorem raw8SideWitnesses_safe :
    ∀ w ∈ raw8SideWitnesses, ∀ m,
      BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m →
      WeightedBound 7014 m := by
  intro w hw m hm
  have hmem : w ∈ witnesses := (List.mem_filter.mp hw).1
  have hcheck : w.check = true :=
    List.all_eq_true.mp witnesses_checked w hmem
  exact w.sound hcheck m hm

theorem raw9SideWitnesses_safe :
    ∀ w ∈ raw9SideWitnesses, ∀ m,
      BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m →
      WeightedBound 7014 m := by
  intro w hw m hm
  have hmem : w ∈ witnesses := (List.mem_filter.mp hw).1
  have hcheck : w.check = true :=
    List.all_eq_true.mp witnesses_checked w hmem
  exact w.sound hcheck m hm

theorem raw23SideWitnesses_safe :
    ∀ w ∈ raw23SideWitnesses, ∀ m,
      BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m →
      WeightedBound 7014 m := by
  intro w hw m hm
  have hmem : w ∈ witnesses := (List.mem_filter.mp hw).1
  have hcheck : w.check = true :=
    List.all_eq_true.mp witnesses_checked w hmem
  exact w.sound hcheck m hm

def raw8Tables : List PartialMachine :=
  raw8SideWitnesses.map fun w => BB6Coverage.unpackTable w.table

def raw9Tables : List PartialMachine :=
  raw9SideWitnesses.map fun w => BB6Coverage.unpackTable w.table

def raw23Tables : List PartialMachine :=
  raw23SideWitnesses.map fun w => BB6Coverage.unpackTable w.table

/-- Exact first-mismatch residual boxes after consuming the checked cylinders. -/
def raw8Remainder : List (BB6.Agent49Box.Box Slot Transition) :=
  BB6.Agent49BoxBridge.remainder raw8Parent raw8Tables

def raw9Remainder : List (BB6.Agent49Box.Box Slot Transition) :=
  BB6.Agent49BoxBridge.remainder raw9Parent raw9Tables

def raw23Remainder : List (BB6.Agent49Box.Box Slot Transition) :=
  BB6.Agent49BoxBridge.remainder raw23Parent raw23Tables

theorem raw8_remainder_exact (m : BB6.Agent49Box.Machine) :
    (∃ r ∈ raw8Remainder, BB6.Agent49Box.Fits r m) ↔
      BB6Coverage.compatible raw8Parent m ∧
        ∀ w ∈ raw8SideWitnesses,
          ¬ BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m := by
  rw [raw8Remainder, BB6.Agent49BoxBridge.remainder_exact]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    intro w hw
    exact hn _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    intro q hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact hn w hw

theorem raw9_remainder_exact (m : BB6.Agent49Box.Machine) :
    (∃ r ∈ raw9Remainder, BB6.Agent49Box.Fits r m) ↔
      BB6Coverage.compatible raw9Parent m ∧
        ∀ w ∈ raw9SideWitnesses,
          ¬ BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m := by
  rw [raw9Remainder, BB6.Agent49BoxBridge.remainder_exact]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    intro w hw
    exact hn _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    intro q hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact hn w hw

theorem raw23_remainder_exact (m : BB6.Agent49Box.Machine) :
    (∃ r ∈ raw23Remainder, BB6.Agent49Box.Fits r m) ↔
      BB6Coverage.compatible raw23Parent m ∧
        ∀ w ∈ raw23SideWitnesses,
          ¬ BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m := by
  rw [raw23Remainder, BB6.Agent49BoxBridge.remainder_exact]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    intro w hw
    exact hn _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    intro q hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact hn w hw

theorem raw8_remainder_disjoint :
    raw8Remainder.Pairwise BB6.Agent49Box.Disjoint :=
  BB6.Agent49BoxBridge.remainder_disjoint _ _

theorem raw9_remainder_disjoint :
    raw9Remainder.Pairwise BB6.Agent49Box.Disjoint :=
  BB6.Agent49BoxBridge.remainder_disjoint _ _

theorem raw23_remainder_disjoint :
    raw23Remainder.Pairwise BB6.Agent49Box.Disjoint :=
  BB6.Agent49BoxBridge.remainder_disjoint _ _

/-- Monotonicity of the weighted bound. -/
theorem weightedBound_mono {b B : Nat} (hB : b ≤ B) {m : BB6.Agent49Box.Machine}
    (hb : WeightedBound b m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (hb k d hk hd) hB

/-- Consume any finite list of checked SideWitness cylinders and retain
    the exact disjoint first-mismatch complement as the remaining obligations. -/
theorem cover_of_sideWitnesses
    (p : PartialMachine) (ws : List SideWitness)
    (hSafe : ∀ w ∈ ws, ∀ m,
      BB6Coverage.compatible (BB6Coverage.unpackTable w.table) m →
      WeightedBound 7014 m)
    (B : Nat) (hB : 7014 ≤ B)
    (remainder : List (BB6.Agent49Box.Box Slot Transition))
    (hRem : remainder =
      BB6.Agent49BoxBridge.remainder p
        (ws.map fun w => BB6Coverage.unpackTable w.table))
    (hOpen : ∀ r ∈ remainder, ∀ m, BB6.Agent49Box.Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) p := by
  subst remainder
  apply BB6.Agent49BoxBridge.coverFromRemainder B p
    (ws.map fun w => BB6Coverage.unpackTable w.table)
  · intro q hq m hm
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact weightedBound_mono hB (hSafe w hw m hm)
  · exact hOpen

theorem raw8_cover (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ raw8Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) raw8Parent :=
  cover_of_sideWitnesses raw8Parent raw8SideWitnesses raw8SideWitnesses_safe
    B hB raw8Remainder rfl hOpen

theorem raw9_cover (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ raw9Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) raw9Parent :=
  cover_of_sideWitnesses raw9Parent raw9SideWitnesses raw9SideWitnesses_safe
    B hB raw9Remainder rfl hOpen

theorem raw23_cover (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ raw23Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) raw23Parent :=
  cover_of_sideWitnesses raw23Parent raw23SideWitnesses raw23SideWitnesses_safe
    B hB raw23Remainder rfl hOpen

/-- The exact canonical78 consumer for the three additional parents plus the
    existing raw10 box bridge. Every other representative remains explicit. -/
theorem exact_from_four_parent_remainders
    (B : Nat) (hB : 7014 ≤ B)
    (hOpen8 : ∀ r ∈ raw8Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m)
    (hOpen9 : ∀ r ∈ raw9Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m)
    (hHeld : ∀ m, BB6Coverage.compatible BB6.Agent49BoxBridge.held m →
      WeightedBound B m)
    (hOpen10 : ∀ r ∈ BB6.Agent49BoxBridge.raw10Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m)
    (hOpen23 : ∀ r ∈ raw23Remainder, ∀ m,
      BB6.Agent49Box.Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ raw8Parent →
      e.2 ≠ raw9Parent →
      e.2 ≠ BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC →
      e.2 ≠ raw23Parent →
      Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47Canonical78.exact_at_target B hB _ champ
  intro e he
  by_cases h8 : e.2 = raw8Parent
  · rw [h8]
    exact raw8_cover B hB hOpen8
  · by_cases h9 : e.2 = raw9Parent
    · rw [h9]
      exact raw9_cover B hB hOpen9
    · by_cases h10 :
        e.2 = BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC
      · rw [h10]
        exact BB6.Agent49BoxBridge.raw10_cover B hB hHeld hOpen10
      · by_cases h23 : e.2 = raw23Parent
        · rw [h23]
          exact raw23_cover B hB hOpen23
        · exact hOther e he h8 h9 h10 h23

/-- Encode the 1-based SideWitness move code. -/
def encodeMove (mv : Move) : Nat :=
  1 + 4 * mv.next.val +
    2 * (if mv.write then 1 else 0) +
    (if mv.right then 1 else 0)

def raw8BranchSlot : Slot := (⟨2, by decide⟩, true)
def raw9BranchSlot : Slot := (⟨2, by decide⟩, false)
def raw23BranchSlot : Slot := (⟨3, by decide⟩, true)

def raw8BranchMoves : List Move :=
  [⟨false, false, ⟨0, by decide⟩⟩,
   ⟨false, true, ⟨0, by decide⟩⟩,
   ⟨true, true, ⟨0, by decide⟩⟩,
   ⟨true, true, ⟨1, by decide⟩⟩]

def raw9BranchMoves : List Move :=
  [⟨false, false, ⟨0, by decide⟩⟩,
   ⟨false, true, ⟨0, by decide⟩⟩,
   ⟨true, true, ⟨0, by decide⟩⟩,
   ⟨false, false, ⟨1, by decide⟩⟩,
   ⟨false, true, ⟨1, by decide⟩⟩,
   ⟨true, true, ⟨1, by decide⟩⟩,
   ⟨false, true, ⟨2, by decide⟩⟩,
   ⟨true, true, ⟨2, by decide⟩⟩]

def raw23BranchMoves : List Move :=
  [⟨false, true, ⟨0, by decide⟩⟩,
   ⟨true, true, ⟨0, by decide⟩⟩,
   ⟨false, true, ⟨1, by decide⟩⟩,
   ⟨true, true, ⟨1, by decide⟩⟩,
   ⟨true, true, ⟨2, by decide⟩⟩]

theorem raw8_whole_branch_count : raw8BranchMoves.length = 4 := by decide
theorem raw9_whole_branch_count : raw9BranchMoves.length = 8 := by decide
theorem raw23_whole_branch_count : raw23BranchMoves.length = 5 := by decide

def raw8BranchPacked (mv : Move) : PackedTable :=
  decodeRows [8, 0, 9, 0, 0, encodeMove mv, 0, 0, 0, 0, 0, 0]

def raw9BranchPacked (mv : Move) : PackedTable :=
  decodeRows [8, 0, 10, 0, encodeMove mv, 0, 0, 0, 0, 0, 0, 0]

def raw23BranchPacked (mv : Move) : PackedTable :=
  decodeRows [8, 0, 12, 0, 13, 0, 0, encodeMove mv, 0, 0, 0, 0]

theorem cover_of_packedWitness (t : PackedTable) (p : PartialMachine)
    (hWitness : hasWitness t = true)
    (hTable : BB6.Agent31FourHoleRoster.sameTable
      (BB6Coverage.unpackTable t) p = true) :
    Cover (WeightedBound 7014) p := by
  apply Cover.leaf p
  intro m hm
  have hEq : BB6Coverage.unpackTable t = p :=
    BB6.Agent31FourHoleRoster.sameTable_sound hTable
  rw [← hEq] at hm
  exact hasWitness_sound t hWitness m hm

theorem raw8_branch_hasWitness (mv : Move) (h : mv ∈ raw8BranchMoves) :
    hasWitness (raw8BranchPacked mv) = true := by
  simp [raw8BranchMoves] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem raw9_branch_hasWitness (mv : Move) (h : mv ∈ raw9BranchMoves) :
    hasWitness (raw9BranchPacked mv) = true := by
  simp [raw9BranchMoves] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem raw23_branch_hasWitness (mv : Move) (h : mv ∈ raw23BranchMoves) :
    hasWitness (raw23BranchPacked mv) = true := by
  simp [raw23BranchMoves] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem raw8_branch_sameTable (mv : Move) (h : mv ∈ raw8BranchMoves) :
    BB6.Agent31FourHoleRoster.sameTable
      (BB6Coverage.unpackTable (raw8BranchPacked mv))
      (BB6Coverage.refine raw8Parent raw8BranchSlot (some mv)) = true := by
  simp [raw8BranchMoves] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem raw9_branch_sameTable (mv : Move) (h : mv ∈ raw9BranchMoves) :
    BB6.Agent31FourHoleRoster.sameTable
      (BB6Coverage.unpackTable (raw9BranchPacked mv))
      (BB6Coverage.refine raw9Parent raw9BranchSlot (some mv)) = true := by
  simp [raw9BranchMoves] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem raw23_branch_sameTable (mv : Move) (h : mv ∈ raw23BranchMoves) :
    BB6.Agent31FourHoleRoster.sameTable
      (BB6Coverage.unpackTable (raw23BranchPacked mv))
      (BB6Coverage.refine raw23Parent raw23BranchSlot (some mv)) = true := by
  simp [raw23BranchMoves] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem raw8_branch_cover (mv : Move) (h : mv ∈ raw8BranchMoves) :
    Cover (WeightedBound 7014)
      (BB6Coverage.refine raw8Parent raw8BranchSlot (some mv)) :=
  cover_of_packedWitness (raw8BranchPacked mv)
    (BB6Coverage.refine raw8Parent raw8BranchSlot (some mv))
    (raw8_branch_hasWitness mv h) (raw8_branch_sameTable mv h)

theorem raw9_branch_cover (mv : Move) (h : mv ∈ raw9BranchMoves) :
    Cover (WeightedBound 7014)
      (BB6Coverage.refine raw9Parent raw9BranchSlot (some mv)) :=
  cover_of_packedWitness (raw9BranchPacked mv)
    (BB6Coverage.refine raw9Parent raw9BranchSlot (some mv))
    (raw9_branch_hasWitness mv h) (raw9_branch_sameTable mv h)

theorem raw23_branch_cover (mv : Move) (h : mv ∈ raw23BranchMoves) :
    Cover (WeightedBound 7014)
      (BB6Coverage.refine raw23Parent raw23BranchSlot (some mv)) :=
  cover_of_packedWitness (raw23BranchPacked mv)
    (BB6Coverage.refine raw23Parent raw23BranchSlot (some mv))
    (raw23_branch_hasWitness mv h) (raw23_branch_sameTable mv h)

#print axioms raw8_in_canonical78
#print axioms raw9_in_canonical78
#print axioms raw23_in_canonical78
#print axioms raw8SideWitnesses_safe
#print axioms raw9SideWitnesses_safe
#print axioms raw23SideWitnesses_safe
#print axioms raw8_remainder_exact
#print axioms raw9_remainder_exact
#print axioms raw23_remainder_exact
#print axioms raw8_remainder_disjoint
#print axioms raw9_remainder_disjoint
#print axioms raw23_remainder_disjoint
#print axioms exact_from_four_parent_remainders
#print axioms raw8_branch_cover
#print axioms raw9_branch_cover
#print axioms raw23_branch_cover

end BB6.Agent2MultiParentSideWitness

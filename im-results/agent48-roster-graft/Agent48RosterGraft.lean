import RosterConvergence
import SevenSideWitnesses

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48RosterGraft

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier
open BB6.Agent13RosterConvergence
open BB6.Agent47SevenSideWitnesses

/-
The four canonical residual cylinders that have exact descendants among
Agent47's checked side-cycle witnesses.  PackedTable order is
A0,A1,B0,B1,C0,C1,D0,D1,E0,E1,F0,F1.
-/
def raw8 : PackedTable :=
  [ some (some ⟨true, true, 1⟩), none,
    some (some ⟨false, false, 2⟩), none,
    none, none, none, none, none, none, none, none ]

def raw9 : PackedTable :=
  [ some (some ⟨true, true, 1⟩), none,
    some (some ⟨false, true, 2⟩), none,
    none, none, none, none, none, none, none, none ]

def raw10 : PackedTable :=
  [ some (some ⟨true, true, 1⟩), none,
    some (some ⟨true, false, 2⟩), none,
    none, none, none, none, none, none, none, none ]

def raw23 : PackedTable :=
  [ some (some ⟨true, true, 1⟩), none,
    some (some ⟨true, true, 2⟩), none,
    some (some ⟨false, false, 3⟩), none,
    none, none, none, none, none, none ]

/-- The first undefined row reached by the blank run in each parent. -/
def slotC0 : Slot := (⟨2, by decide⟩, false)
def slotC1 : Slot := (⟨2, by decide⟩, true)
def slotD1 : Slot := (⟨3, by decide⟩, true)

/-- All 25 possible row values: halt, followed by the 24 ordinary moves. -/
def allChoices : List (Option Move) := none :: allMoves.map some

/-- The 25 exact child cylinders obtained by fixing one previously
    unassigned transition row. -/
def splitChildren (t : PackedTable) (s : Slot) : List PackedTable :=
  allChoices.map fun choice => packTable (refine (unpackTable t) s choice)

/-- Keep precisely those children not already discharged by an exact
    Agent47 side-cycle witness. -/
def openChildren (t : PackedTable) (s : Slot) : List PackedTable :=
  (splitChildren t s).filter fun child => !(hasWitness child)

/-- Replace every occurrence of one packed cylinder by a finite list of
    subcylinders. -/
def replacePacked (target : PackedTable) (replacement : List PackedTable)
    (r : List PackedTable) : List PackedTable :=
  r.flatMap fun t => if t = target then replacement else [t]

def graftOne (t : PackedTable) (s : Slot) (r : List PackedTable) : List PackedTable :=
  replacePacked t (openChildren t s) r

/-- A table frontier is complete at weighted bound B when every completion
    of the first-one root is either bounded or extends a listed residual. -/
def RootCovered (B : Nat) (r : List PackedTable) : Prop :=
  ∀ m, compatible BB6.Agent50TNFPilot.root m →
    WeightedBound B m ∨ ∃ t ∈ r, compatible (unpackTable t) m

theorem weightedBound_mono {B C : Nat} (hBC : B ≤ C) {m : Machine}
    (h : WeightedBound B m) : WeightedBound C m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hBC

theorem splitChildren_cover (t : PackedTable) (s : Slot) (m : Machine)
    (hm : compatible (unpackTable t) m) :
    ∃ child ∈ splitChildren t s, compatible (unpackTable child) m := by
  let choice : Option Move := m s
  have hchoice : choice ∈ allChoices := by
    cases h : m s with
    | none => simp [allChoices]
    | some mv => simp [allChoices, allMoves_complete mv]
  refine ⟨packTable (refine (unpackTable t) s choice), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨choice, hchoice, rfl⟩
  · simpa [choice, unpack_packTable] using
      (compatible_refine (unpackTable t) m s hm)

theorem openChildren_sound (t : PackedTable) (s : Slot) :
    ∀ m, compatible (unpackTable t) m →
      WeightedBound 7014 m ∨
        ∃ child ∈ openChildren t s, compatible (unpackTable child) m := by
  intro m hm
  obtain ⟨child, hchild, hcomp⟩ := splitChildren_cover t s m hm
  by_cases hw : hasWitness child = true
  · exact Or.inl (hasWitness_sound child hw m hcomp)
  · exact Or.inr ⟨child,
      List.mem_filter.mpr ⟨hchild, by simp [openChildren, hw]⟩, hcomp⟩

theorem replacePacked_sound (target : PackedTable) (replacement : List PackedTable)
    (r : List PackedTable) (h : RootCovered 7014 r)
    (hrep : ∀ m, compatible (unpackTable target) m →
      WeightedBound 7014 m ∨
        ∃ child ∈ replacement, compatible (unpackTable child) m) :
    RootCovered 7014 (replacePacked target replacement r) := by
  intro m hm
  rcases h m hm with hbound | ⟨t, ht, hcomp⟩
  · exact Or.inl hbound
  · by_cases hEq : t = target
    · subst t
      rcases hrep m hcomp with hbound | ⟨child, hchild, hchildComp⟩
      · exact Or.inl hbound
      · apply Or.inr
        refine ⟨child, List.mem_flatMap.mpr ⟨target, ht, ?_⟩, hchildComp⟩
        simpa [replacePacked] using hchild
    · apply Or.inr
      refine ⟨t, List.mem_flatMap.mpr ⟨t, ht, ?_⟩, hcomp⟩
      simp [replacePacked, hEq]

theorem graftOne_sound (t : PackedTable) (s : Slot) (r : List PackedTable)
    (h : RootCovered 7014 r) :
    RootCovered 7014 (graftOne t s r) := by
  apply replacePacked_sound t (openChildren t s) r h
  intro m hm
  exact openChildren_sound t s m hm

theorem canonicalRoster_sound_7014 : RootCovered 7014 canonicalResidualRoster := by
  intro m hm
  rcases canonicalResidualRoster_sound_395 m hm with hbound | ⟨t, ht, hcomp⟩
  · exact Or.inl (weightedBound_mono (by decide : 395 ≤ 7014) hbound)
  · exact Or.inr ⟨t, ht, hcomp⟩

/-- The 124-table canonical roster with the 18 exact Agent47 child cylinders
    removed.  All other children of the four split parents remain open. -/
def graftedRoster : List PackedTable :=
  graftOne raw23 slotD1
    (graftOne raw10 slotC1
      (graftOne raw9 slotC0
        (graftOne raw8 slotC1 canonicalResidualRoster)))

theorem graftedRoster_sound_7014 : RootCovered 7014 graftedRoster := by
  unfold graftedRoster
  apply graftOne_sound
  apply graftOne_sound
  apply graftOne_sound
  apply graftOne_sound
  exact canonicalRoster_sound_7014

/-- The four parent tables are literal members of the canonical 124 roster. -/
theorem raw8_mem : raw8 ∈ canonicalResidualRoster := by decide
theorem raw9_mem : raw9 ∈ canonicalResidualRoster := by decide
theorem raw10_mem : raw10 ∈ canonicalResidualRoster := by decide
theorem raw23_mem : raw23 ∈ canonicalResidualRoster := by decide

/-- These are genuine holes, so each 25-way split is an exact partition. -/
theorem raw8_slot_hole : unpackTable raw8 slotC1 = none := by decide
theorem raw9_slot_hole : unpackTable raw9 slotC0 = none := by decide
theorem raw10_slot_hole : unpackTable raw10 slotC1 = none := by decide
theorem raw23_slot_hole : unpackTable raw23 slotD1 = none := by decide

/-- Exact residual and closed-child cardinalities for the graft. -/
theorem raw8_open_count : (openChildren raw8 slotC1).length = 21 := by decide
theorem raw9_open_count : (openChildren raw9 slotC0).length = 17 := by decide
theorem raw10_open_count : (openChildren raw10 slotC1).length = 24 := by decide
theorem raw23_open_count : (openChildren raw23 slotD1).length = 20 := by decide

def closedChildren : List PackedTable :=
  (splitChildren raw8 slotC1).filter hasWitness ++
  (splitChildren raw9 slotC0).filter hasWitness ++
  (splitChildren raw10 slotC1).filter hasWitness ++
  (splitChildren raw23 slotD1).filter hasWitness

theorem closedChildren_count : closedChildren.length = 18 := by decide

theorem graftedRoster_count : graftedRoster.length = 202 := by decide

#print axioms graftedRoster_sound_7014
#print axioms graftedRoster_count

end BB6.Agent48RosterGraft

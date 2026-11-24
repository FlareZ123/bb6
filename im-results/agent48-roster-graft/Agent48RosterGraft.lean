import RosterConvergence
import SideWitnessCore

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
The four canonical residual cylinders that have exact side-cycle descendants.
PackedTable order is A0,A1,B0,B1,C0,C1,D0,D1,E0,E1,F0,F1.
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

/-- Slots used by the adaptive side-witness decision trees. -/
def slotB1 : Slot := (⟨1, by decide⟩, true)
def slotC0 : Slot := (⟨2, by decide⟩, false)
def slotC1 : Slot := (⟨2, by decide⟩, true)
def slotD0 : Slot := (⟨3, by decide⟩, false)
def slotD1 : Slot := (⟨3, by decide⟩, true)
def slotE0 : Slot := (⟨4, by decide⟩, false)
def slotE1 : Slot := (⟨4, by decide⟩, true)
def slotF0 : Slot := (⟨5, by decide⟩, false)

/-- Refine one packed table by one exact transition choice. -/
def refinePacked (t : PackedTable) (s : Slot) (choice : Option Move) : PackedTable :=
  packTable (refine (unpackTable t) s choice)

/-
Adaptive split targets.  A target is reached only along the assignments
listed in its definition; every target slot below is still unassigned.
The action numerals in the comments are 1-based allMoves indices.
-/
def raw8a : PackedTable := refinePacked raw8 slotC1 (some ⟨true, false, 3⟩) -- C1=15
def raw8b : PackedTable := refinePacked raw8a slotD0 (some ⟨false, false, 1⟩) -- D0=5
def raw8c : PackedTable := refinePacked raw8b slotC0 (some ⟨true, true, 2⟩) -- C0=12

def raw9a : PackedTable := refinePacked raw9 slotC0 (some ⟨true, false, 0⟩) -- C0=3
def raw9b : PackedTable := refinePacked raw9a slotB1 (some ⟨false, false, 3⟩) -- B1=13
def raw9c : PackedTable := refinePacked raw9b slotD1 (some ⟨true, false, 3⟩) -- D1=15

def raw10a : PackedTable := refinePacked raw10 slotC1 (some ⟨false, false, 3⟩) -- C1=13
def raw10b : PackedTable := refinePacked raw10a slotD0 (some ⟨true, false, 2⟩) -- D0=11
def raw10c : PackedTable := refinePacked raw10b slotC0 (some ⟨false, false, 4⟩) -- C0=17

def raw23a : PackedTable := refinePacked raw23 slotD1 (some ⟨true, false, 4⟩) -- D1=19
def raw23b : PackedTable := refinePacked raw23a slotE1 (some ⟨false, false, 1⟩) -- E1=5
def raw23c : PackedTable := refinePacked raw23b slotE0 (some ⟨true, false, 3⟩) -- E0=15
def raw23d : PackedTable := refinePacked raw23a slotE1 (some ⟨true, false, 5⟩) -- E1=23
def raw23e : PackedTable := refinePacked raw23d slotF0 (some ⟨true, false, 2⟩) -- F0=11

/-- All 25 possible row values: halt, followed by the 24 ordinary moves. -/
def allChoices : List (Option Move) := none :: allMoves.map some

/-- The 25 exact child cylinders obtained by fixing one transition row. -/
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
    change m s ∈ allChoices
    cases h : m s with
    | none => simp [allChoices]
    | some mv =>
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨mv, allMoves_complete mv, rfl⟩
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
      List.mem_filter.mpr ⟨hchild, by simp [hw]⟩, hcomp⟩

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

/-- Adaptive depth-four graft of the 388 exact side-cycle witnesses into the
    canonical first-one roster.  Eighteen split nodes discharge 115 leaves. -/
def graftedRoster : List PackedTable :=
  graftOne raw23e slotD0
    (graftOne raw23d slotF0
      (graftOne raw23c slotC1
        (graftOne raw23b slotE0
          (graftOne raw23a slotE1
            (graftOne raw23 slotD1
              (graftOne raw10c slotE0
                (graftOne raw10b slotC0
                  (graftOne raw10a slotD0
                    (graftOne raw10 slotC1
                      (graftOne raw9c slotD0
                        (graftOne raw9b slotD1
                          (graftOne raw9a slotB1
                            (graftOne raw9 slotC0
                              (graftOne raw8c slotD1
                                (graftOne raw8b slotC0
                                  (graftOne raw8a slotD0
                                    (graftOne raw8 slotC1 canonicalResidualRoster)))))))))))))))))))

theorem graftedRoster_sound_7014 : RootCovered 7014 graftedRoster := by
  unfold graftedRoster
  repeat apply graftOne_sound
  exact canonicalRoster_sound_7014

/-- The four parent tables are literal members of the canonical 124 roster. -/
theorem raw8_mem : raw8 ∈ canonicalResidualRoster := by decide
theorem raw9_mem : raw9 ∈ canonicalResidualRoster := by decide
theorem raw10_mem : raw10 ∈ canonicalResidualRoster := by decide
theorem raw23_mem : raw23 ∈ canonicalResidualRoster := by decide

/-- All 18 selected split rows are genuinely unassigned. -/
theorem raw8_slot_hole : unpackTable raw8 slotC1 = none := by decide
theorem raw8a_slot_hole : unpackTable raw8a slotD0 = none := by decide
theorem raw8b_slot_hole : unpackTable raw8b slotC0 = none := by decide
theorem raw8c_slot_hole : unpackTable raw8c slotD1 = none := by decide

theorem raw9_slot_hole : unpackTable raw9 slotC0 = none := by decide
theorem raw9a_slot_hole : unpackTable raw9a slotB1 = none := by decide
theorem raw9b_slot_hole : unpackTable raw9b slotD1 = none := by decide
theorem raw9c_slot_hole : unpackTable raw9c slotD0 = none := by decide

theorem raw10_slot_hole : unpackTable raw10 slotC1 = none := by decide
theorem raw10a_slot_hole : unpackTable raw10a slotD0 = none := by decide
theorem raw10b_slot_hole : unpackTable raw10b slotC0 = none := by decide
theorem raw10c_slot_hole : unpackTable raw10c slotE0 = none := by decide

theorem raw23_slot_hole : unpackTable raw23 slotD1 = none := by decide
theorem raw23a_slot_hole : unpackTable raw23a slotE1 = none := by decide
theorem raw23b_slot_hole : unpackTable raw23b slotE0 = none := by decide
theorem raw23c_slot_hole : unpackTable raw23c slotC1 = none := by decide
theorem raw23d_slot_hole : unpackTable raw23d slotF0 = none := by decide
theorem raw23e_slot_hole : unpackTable raw23e slotD0 = none := by decide

/-- Exact side-cycle leaves removed at every internal split node. -/
def closedChildren : List PackedTable :=
  (splitChildren raw8 slotC1).filter hasWitness ++
  (splitChildren raw8a slotD0).filter hasWitness ++
  (splitChildren raw8b slotC0).filter hasWitness ++
  (splitChildren raw8c slotD1).filter hasWitness ++
  (splitChildren raw9 slotC0).filter hasWitness ++
  (splitChildren raw9a slotB1).filter hasWitness ++
  (splitChildren raw9b slotD1).filter hasWitness ++
  (splitChildren raw9c slotD0).filter hasWitness ++
  (splitChildren raw10 slotC1).filter hasWitness ++
  (splitChildren raw10a slotD0).filter hasWitness ++
  (splitChildren raw10b slotC0).filter hasWitness ++
  (splitChildren raw10c slotE0).filter hasWitness ++
  (splitChildren raw23 slotD1).filter hasWitness ++
  (splitChildren raw23a slotE1).filter hasWitness ++
  (splitChildren raw23b slotE0).filter hasWitness ++
  (splitChildren raw23c slotC1).filter hasWitness ++
  (splitChildren raw23d slotF0).filter hasWitness ++
  (splitChildren raw23e slotD0).filter hasWitness

theorem closedChildren_count : closedChildren.length = 115 := by decide

theorem graftedRoster_count : graftedRoster.length = 441 := by decide

#print axioms graftedRoster_sound_7014
#print axioms graftedRoster_count

end BB6.Agent48RosterGraft

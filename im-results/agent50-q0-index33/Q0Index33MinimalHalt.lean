import WeightedBoxMinimalHalt
import SparseBlankDelay

namespace BB6.Agent50Q0Index33

open BB6Coverage
open BB6.Agent49Box
open BB6.Agent13BlankDelay
open BB6.Agent13BoxMinimalHalt

/-- The sole post-decider open table at q0 sibling-scan index 33:
    1RB1RD 1RC0RE 0LA--- 1LA1LD 0LF0RB 1LF0LC.
    Its only unassigned slot is C1. -/
def residual : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, ⟨1, by decide⟩⟩)
  | 0, true  => some (some ⟨true, true, ⟨3, by decide⟩⟩)
  | 1, false => some (some ⟨true, true, ⟨2, by decide⟩⟩)
  | 1, true  => some (some ⟨false, true, ⟨4, by decide⟩⟩)
  | 2, false => some (some ⟨false, false, ⟨0, by decide⟩⟩)
  | 2, true  => none
  | 3, false => some (some ⟨true, false, ⟨0, by decide⟩⟩)
  | 3, true  => some (some ⟨true, false, ⟨3, by decide⟩⟩)
  | 4, false => some (some ⟨false, false, ⟨5, by decide⟩⟩)
  | 4, true  => some (some ⟨false, true, ⟨1, by decide⟩⟩)
  | 5, false => some (some ⟨true, false, ⟨5, by decide⟩⟩)
  | 5, true  => some (some ⟨false, false, ⟨2, by decide⟩⟩)

def haltSlot : Slot := (⟨2, by decide⟩, true)
def haltCompletion : Machine := fun s => (residual s).getD none

def residualBox : Box Slot Transition := fun s =>
  match residual s with
  | none => choices
  | some t => [t]

def slots : List Slot :=
  (List.finRange 6).flatMap fun q => [(q, false), (q, true)]

theorem compatible_iff_fits (m : Machine) :
    compatible residual m ↔ Fits residualBox m := by
  constructor
  · intro h s
    cases hp : residual s with
    | none => simpa [residualBox, hp] using choices_complete (m s)
    | some t => simp [residualBox, hp, h s t hp]
  · intro h s t hp
    have hs : m s ∈ [t] := by simpa [residualBox, hp] using h s
    simpa using hs

theorem haltCompletion_compatible : compatible residual haltCompletion := by
  intro s t hs
  simp [haltCompletion, hs]

theorem haltCompletion_missing_iff :
    ∀ s, haltCompletion s = none ↔ s = haltSlot := by
  decide

def boxMass (b : Box Slot Transition) : Nat :=
  (slots.map fun s => (b s).length).prod

def sliceMasses : List Nat :=
  slots.map fun s => boxMass (minimalSlice residualBox s)

theorem residual_box_mass : boxMass residualBox = 25 := by decide

theorem one_halt_slice_masses :
    sliceMasses = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] := by decide

theorem c1_slice_singleton :
    ∀ s, minimalSlice residualBox haltSlot s = [haltCompletion s] := by
  decide

theorem haltCompletion_fits_c1_slice :
    Fits (minimalSlice residualBox haltSlot) haltCompletion := by
  intro s
  rw [c1_slice_singleton]
  simp

theorem c1_slice_unique (m : Machine)
    (hm : Fits (minimalSlice residualBox haltSlot) m) :
    m = haltCompletion := by
  funext s
  have hs := hm s
  rw [c1_slice_singleton] at hs
  simpa using hs

theorem other_slice_empty_at_slot :
    ∀ s, s ≠ haltSlot → minimalSlice residualBox s s = [] := by
  decide

theorem no_fit_other_slice (s : Slot) (hs : s ≠ haltSlot) (m : Machine) :
    ¬ Fits (minimalSlice residualBox s) m := by
  intro hm
  have hmem := hm s
  rw [other_slice_empty_at_slot s hs] at hmem
  simp at hmem

theorem residual_weightedBound_iff (B : Nat) :
    (∀ m, compatible residual m → WeightedBound B m) ↔
      WeightedBound B haltCompletion := by
  calc
    (∀ m, compatible residual m → WeightedBound B m) ↔
        (∀ m, Fits residualBox m → WeightedBound B m) := by
          constructor
          · intro h m hm
            exact h m ((compatible_iff_fits m).2 hm)
          · intro h m hm
            exact h m ((compatible_iff_fits m).1 hm)
    _ ↔ (∀ s m, Fits (minimalSlice residualBox s) m → WeightedBound B m) :=
      minimalSlices_iff residualBox B
    _ ↔ WeightedBound B haltCompletion := by
      constructor
      · intro h
        exact h haltSlot haltCompletion haltCompletion_fits_c1_slice
      · intro h s m hm
        by_cases hs : s = haltSlot
        · subst s
          rw [c1_slice_unique hm]
          exact h
        · exact False.elim (no_fit_other_slice s hs m hm)

theorem residual_weightedBound_of_neverHalts (B : Nat)
    (h : NeverHalts haltCompletion) :
    ∀ m, compatible residual m → WeightedBound B m := by
  apply (residual_weightedBound_iff B).2
  exact weighted_never B haltCompletion h

end BB6.Agent50Q0Index33

import Lean

open List

namespace BB6CrossRouteHeldLeaf

abbrev Move := Fin 24
abbrev Transition := Option Move
abbrev PartialTable := Fin 12 → Option Transition
abbrev Machine := Fin 12 → Transition

def setMove (mv : Move) : Option (Option Move) := some (some mv)

def heldTable : PartialTable := fun i =>
  match i.val with
  | 0 => setMove ⟨7, by decide⟩   -- A0 = 1RB
  | 1 => setMove ⟨13, by decide⟩  -- A1 = 0RD
  | 2 => setMove ⟨10, by decide⟩  -- B0 = 1LC
  | 3 => setMove ⟨6, by decide⟩   -- B1 = 1LB
  | 4 => setMove ⟨16, by decide⟩  -- C0 = 0LE
  | 5 => setMove ⟨3, by decide⟩   -- C1 = 1RA
  | 6 => setMove ⟨8, by decide⟩   -- D0 = 0LC
  | 7 => setMove ⟨1, by decide⟩   -- D1 = 0RA
  | 8 => setMove ⟨22, by decide⟩  -- E0 = 1LF
  | 9 => setMove ⟨14, by decide⟩  -- E1 = 1LD
  | 10 => setMove ⟨15, by decide⟩ -- F0 = 1RD
  | _ => none                     -- F1 is the unique unassigned query

def rootResidual : PartialTable := fun i =>
  match i.val with
  | 0 => setMove ⟨7, by decide⟩   -- A0 = 1RB
  | 2 => setMove ⟨10, by decide⟩  -- B0 = 1LC
  | _ => none

def refines (child parent : PartialTable) : Prop :=
  ∀ i, parent i = none ∨ child i = parent i

def compatible (p : PartialTable) (m : Machine) : Prop :=
  ∀ i, p i = none ∨ p i = some (m i)

def refinesB (child parent : PartialTable) : Bool :=
  (List.finRange 12).all fun i => decide (parent i = none ∨ child i = parent i)

theorem refinesB_sound {child parent : PartialTable}
    (h : refinesB child parent = true) : refines child parent := by
  intro i
  have hi := (List.all_eq_true.mp h) i (List.mem_finRange i)
  exact of_decide_eq_true hi

def holeCount (p : PartialTable) : Nat :=
  ((List.finRange 12).filter fun i => decide (p i = none)).length

def newSlots : List (Fin 12) :=
  (List.finRange 12).filter fun i =>
    decide (rootResidual i = none ∧ heldTable i ≠ none)

def targetState (mv : Move) : Fin 6 :=
  ⟨mv.val / 4, by omega⟩

def targetStates (p : PartialTable) : List (Fin 6) :=
  (List.finRange 12).filterMap fun i =>
    match p i with
    | some (some mv) => some (targetState mv)
    | _ => none

def introducedB (p : PartialTable) (q : Fin 6) : Bool :=
  q.val == 0 || (targetStates p).any (fun r => decide (r = q))

def freshCut (p : PartialTable) : Nat :=
  ((List.finRange 6).takeWhile (introducedB p)).length

theorem held_refines_root : refines heldTable rootResidual := by
  apply refinesB_sound
  decide

theorem held_hole_count : holeCount heldTable = 1 := by decide
theorem root_hole_count : holeCount rootResidual = 10 := by decide
theorem held_new_slot_count : newSlots.length = 9 := by decide
theorem held_fresh_cut : freshCut heldTable = 6 := by decide

theorem held_only_hole_is_F1 :
    (List.finRange 12).filter (fun i => decide (heldTable i = none)) =
      [⟨11, by decide⟩] := by decide

theorem held_root_A0 : heldTable ⟨0, by decide⟩ = setMove ⟨7, by decide⟩ := by decide
theorem held_root_B0 : heldTable ⟨2, by decide⟩ = setMove ⟨10, by decide⟩ := by decide

/-- Every completion of the parent residual either lies in the certified
    held leaf or disagrees at one of the nine newly fixed transition slots. -/
theorem held_leaf_partition (m : Machine) (hm : compatible rootResidual m) :
    compatible heldTable m ∨
      ∃ i ∈ newSlots, ∃ t, heldTable i = some t ∧ m i ≠ t := by
  classical
  by_cases hc : compatible heldTable m
  · exact Or.inl hc
  · right
    have hbad : ∃ i, heldTable i ≠ none ∧ heldTable i ≠ some (m i) := by
      unfold compatible at hc
      obtain ⟨i, hi⟩ := Classical.not_forall.mp hc
      exact ⟨i, (fun h => hi (Or.inl h)), (fun h => hi (Or.inr h))⟩
    obtain ⟨i, hnotNone, hnotMatch⟩ := hbad
    have hparentNone : rootResidual i = none := by
      apply Classical.byContradiction
      intro hparent
      have hchildParent : heldTable i = rootResidual i :=
        (held_refines_root i).resolve_left hparent
      have hparentMachine : rootResidual i = some (m i) :=
        (hm i).resolve_left hparent
      exact hnotMatch (hchildParent.trans hparentMachine)
    have hmem : i ∈ newSlots := by
      apply List.mem_filter.mpr
      constructor
      · exact List.mem_finRange i
      · exact of_decide_eq_true (by simp [hparentNone, hnotNone])
    cases hchild : heldTable i with
    | none => contradiction
    | some t =>
      have hneq : m i ≠ t := by
        intro hEq
        apply hnotMatch
        rw [hchild, hEq]
      exact ⟨i, hmem, t, hchild, hneq⟩

/-- q_i 2800, size-100 held checkpoint: eleven fixed transitions,
    one remaining query, and all six states introduced. -/
def checkpointOffset : Nat := 2800
def checkpointSize : Nat := 100

theorem checkpoint_metadata :
    (checkpointOffset, checkpointSize, holeCount heldTable, freshCut heldTable) =
      (2800, 100, 1, 6) := by decide

#print axioms held_refines_root
#print axioms held_hole_count
#print axioms held_new_slot_count
#print axioms held_fresh_cut
#print axioms held_leaf_partition
#print axioms checkpoint_metadata

end BB6CrossRouteHeldLeaf

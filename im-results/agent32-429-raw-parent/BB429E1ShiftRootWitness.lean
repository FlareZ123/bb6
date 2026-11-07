import BB429PhysicalFrontier
import Lean

namespace BB429E1ShiftRootWitness
open BB6Coverage

/-- The blank initial configuration for the six-state machine #429. -/
def blank : Config :=
  { state := ⟨0, by decide⟩
    head := 0
    tape := fun _ => false }

/-- The finite left and right windows around a physical head. -/
def leftWindow (c : Config) (n : Nat) : List Bool :=
  (List.range n).map fun i => c.tape (c.head - ((i : Int) + 1))

def rightWindow (c : Config) (n : Nat) : List Bool :=
  (List.range n).map fun i => c.tape (c.head + ((i : Int) + 1))

/-- Exact local observation of the blank run at a specified time. -/
def obsWindow (n : Nat) : Option (Nat × Int × Bool × List Bool × List Bool) :=
  (BB6Coverage.run target429 n blank).map fun c =>
    (c.state.val, c.head, c.tape c.head, leftWindow c 11, rightWindow c 8)

/-- A compact state/head/current observation, with a sentinel for a missing run. -/
def obsAt (n : Nat) : Nat × Int × Bool :=
  match BB6Coverage.run target429 n blank with
  | some c => (c.state.val, c.head, c.tape c.head)
  | none => (99, 0, false)

/-- The blank orbit reaches an E/1 configuration with eleven ones immediately
    to the left and six ones followed by 0,1 immediately to the right. This is
    the concrete k=3 start shape of the upstream `shift_E_11` helper. -/
theorem root_reaches_first_shift_start :
    obsWindow 122 =
      some (4, 4, true, List.replicate 11 true,
        List.replicate 6 true ++ [false, true]) := by
  native_decide

/-- The six consecutive E/1 instructions of the first shift sweep, including
    every intermediate head position. -/
theorem root_first_shift_trace :
    (List.range 7).map (fun j => obsAt (122+j)) =
      [(4, 4, true), (4, 3, true), (4, 2, true), (4, 1, true),
       (4, 0, true), (4, -1, true), (4, -2, true)] := by
  native_decide

/-- All E/1 writer coordinates in the first 808 raw instructions. -/
def e1WriterPositionsBefore (n : Nat) : List Int :=
  (List.range n).filterMap fun t =>
    match BB6Coverage.run target429 t blank with
    | some c =>
        if c.state.val == 4 && c.tape c.head then some c.head else none
    | none => none

/-- In the first 808 raw instructions, every E/1 write is at or left of
    coordinate 16, and the head is at coordinate 16 at step 808. Thus every
    E/1 write in this finite prefix has a later head at or to its right. -/
theorem root_e1_writers_closed_by_808 :
    (e1WriterPositionsBefore 808).all (fun x => decide (x ≤ 16)) = true ∧
    obsAt 808 = (0, 16, true) := by
  native_decide

theorem root_every_initial_e1_writer_revisited :
    ∀ x, x ∈ e1WriterPositionsBefore 808 → x ≤ (obsAt 808).2.1 := by
  intro x hx
  have hbound := (List.all_eq_true.mp root_e1_writers_closed_by_808.1) x hx
  have hhead : (obsAt 808).2.1 = 16 := by
    simp [root_e1_writers_closed_by_808.2]
  rw [hhead]
  simpa using hbound

/-- The head later returns to the first shift cell (coordinate 4) at step 192.
    Hence none of the six E/1 writes in this *first* sweep is a global
    last-writer candidate for a later fatal C/01 event. -/
theorem root_revisits_first_shift_start :
    obsAt 192 = (0, 4, true) := by
  native_decide

#print axioms root_reaches_first_shift_start
#print axioms root_first_shift_trace
#print axioms root_revisits_first_shift_start
#print axioms root_e1_writers_closed_by_808
#print axioms root_every_initial_e1_writer_revisited

end BB429E1ShiftRootWitness

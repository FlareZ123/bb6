import Frontier

namespace BB6Coverage

/-- A drifting head on a pristine tape, with all cells still zero. -/
def emptyAt (p : Int) : Config :=
  {state := ⟨0, by decide⟩, head := p, tape := fun _ => false}

@[simp] theorem blank_emptyAt : blank = emptyAt 0 := rfl
@[simp] theorem emptyAt_read (p : Int) : readSlot (emptyAt p) = initialSlot := rfl

def blankDrift (right : Bool) : Move :=
  {write := false, right := right, next := ⟨0, by decide⟩}

/-- The first A/0 instruction writes 0, moves left or right, and returns to A;
    a pristine tape remains pristine forever. -/
theorem blankDrift_step (m : Machine) (right : Bool) (p : Int)
    (hm : m initialSlot = some (blankDrift right)) :
    rawStep m (emptyAt p) =
      some (emptyAt (p + (if right then 1 else -1))) := by
  simp only [rawStep, emptyAt_read, hm, Option.map_some]
  apply congrArg some
  cases right <;> simp [applyMove, emptyAt, blankDrift] <;>
    (funext x; by_cases hx : x = p <;> simp [hx])

def driftPosition (right : Bool) (n : Nat) : Int :=
  if right then n else -(n : Int)

@[simp] theorem driftPosition_zero (b : Bool) : driftPosition b 0 = 0 := by
  cases b <;> rfl

@[simp] theorem driftPosition_succ (b : Bool) (n : Nat) :
    driftPosition b (n+1) = driftPosition b n + (if b then 1 else -1) := by
  cases b <;> simp [driftPosition] <;> omega

/-- Uniform exact infinite run, for *any* choices of the other 11 entries. -/
theorem blankDrift_run (m : Machine) (right : Bool) (n : Nat)
    (hm : m initialSlot = some (blankDrift right)) :
    run m n blank = some (emptyAt (driftPosition right n)) := by
  induction n with
  | zero => simp [run, blank_emptyAt]
  | succ n ih =>
    simp only [run, ih, Option.bind_some, blankDrift_step m right _ hm,
      driftPosition_succ]

/-- A genuinely infinite nonhalting leaf in the sparse coverage tree. -/
theorem blankDrift_never (m : Machine) (right : Bool)
    (hm : m initialSlot = some (blankDrift right)) : NeverHalts m := by
  intro n
  rw [blankDrift_run m right n hm]
  rfl

def driftLeaf (right : Bool) : PartialMachine :=
  refine emptyTable initialSlot (some (blankDrift right))

theorem driftLeaf_certificate (right : Bool) (bound : Nat) :
    Cover (DecidedBelow bound) (driftLeaf right) := by
  apply Cover.leaf
  intro m hm
  left
  apply blankDrift_never m right
  exact hm initialSlot (some (blankDrift right)) (by simp [driftLeaf,refine])

#print axioms blankDrift_step
#print axioms blankDrift_run
#print axioms blankDrift_never
#print axioms driftLeaf_certificate
end BB6Coverage

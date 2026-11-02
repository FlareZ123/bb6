import Frontier

namespace BB6Coverage

/-- A fully specified final transition can write and move before entering Z.
    All four final actions count one step toward runtime. -/
structure FinalAction where
  write : Bool
  right : Bool
  deriving DecidableEq, Repr

inductive RawAction where
  | go : Move → RawAction
  | stop : FinalAction → RawAction
  deriving DecidableEq, Repr

abbrev ExplicitMachine := Slot → RawAction

/-- Erase the final write/direction while retaining every ordinary transition. -/
def eraseFinal (m : ExplicitMachine) : Machine := fun slot =>
  match m slot with
  | .go t => some t
  | .stop _ => none

/-- A configuration even after a final writing/moving halt action. -/
def afterFinal (c : Config) (h : FinalAction) : Config :=
  { state := c.state
    head := c.head + (if h.right then 1 else -1)
    tape := fun x => if x = c.head then h.write else c.tape x }

inductive RawOutcome where
  | running : Config → RawOutcome
  | halted : Config → RawOutcome

def detailedStep (m : ExplicitMachine) : RawOutcome → RawOutcome
  | .halted c => .halted c
  | .running c =>
    match m (readSlot c) with
    | .go t => .running (applyMove c t)
    | .stop h => .halted (afterFinal c h)

/-- The outcome after exactly n attempted instructions. -/
def detailedRun (m : ExplicitMachine) : Nat → Config → RawOutcome
  | 0, c => .running c
  | n+1, c => detailedStep m (detailedRun m n c)

/-- Forget the final tape and head, but preserve the running/halting status. -/
def project : RawOutcome → Option Config
  | .running c => some c
  | .halted _ => none

/-- Step-by-step commuting diagram between explicit halting transitions and
    implicit undefined-transition semantics. -/
theorem project_step (m : ExplicitMachine) (o : RawOutcome) :
    project (detailedStep m o) =
      (project o).bind (rawStep (eraseFinal m)) := by
  cases o with
  | halted c => rfl
  | running c =>
    simp only [detailedStep, project, Option.bind_some]
    cases h : m (readSlot c) with
    | go t => simp [rawStep, eraseFinal, h]
    | stop t => simp [rawStep, eraseFinal, h]

theorem project_run (m : ExplicitMachine) (n : Nat) (c : Config) :
    project (detailedRun m n c) = run (eraseFinal m) n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [detailedRun, project_step, ih]
    rfl

private theorem exists_running_iff (o : RawOutcome) :
    (∃ c, o = .running c) ↔ (project o).isSome = true := by
  cases o with
  | running c => simp [project]
  | halted c => simp [project]

private theorem exists_halted_iff (o : RawOutcome) :
    (∃ c, o = .halted c) ↔ project o = none := by
  cases o with
  | running c => simp [project]
  | halted c => simp [project]

/-- Count n ordinary instructions followed by the one final halt instruction.
    The exact final write and direction are present in the concrete outcome. -/
def ExplicitHaltsAfter (m : ExplicitMachine) (n : Nat) : Prop :=
  (∃ c, detailedRun m n blank = .running c) ∧
  (∃ c, detailedRun m (n+1) blank = .halted c)

/-- Exact time-preserving semantics bridge, for *all* six-state explicit
    tables and all times, independent of the terminal write and direction. -/
theorem explicit_halts_iff_implicit (m : ExplicitMachine) (n : Nat) :
    ExplicitHaltsAfter m n ↔ HaltsAfter (eraseFinal m) n := by
  unfold ExplicitHaltsAfter HaltsAfter
  rw [exists_running_iff, exists_halted_iff]
  rw [project_run, project_run]

/-- No additional subtlety about infinite runs: nonhalting is likewise
    invariant under erasing the terminal action from the table. -/
def ExplicitNeverHalts (m : ExplicitMachine) : Prop :=
  ∀ n, ∃ c, detailedRun m n blank = .running c

theorem explicit_never_iff_implicit (m : ExplicitMachine) :
    ExplicitNeverHalts m ↔ NeverHalts (eraseFinal m) := by
  unfold ExplicitNeverHalts NeverHalts
  simp only [exists_running_iff, project_run]

/-- There are exactly four concrete terminal instructions. Each has the
    same time semantics as one implicit halt; this statement concerns S(6)
    runtime only, not the number of 1s left on tape. -/
def finalActions : List FinalAction :=
  [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]

theorem four_final_actions : finalActions.length = 4 := by decide

theorem each_final_action_listed (h : FinalAction) : h ∈ finalActions := by
  rcases h with ⟨w, r⟩
  cases w <;> cases r <;> simp [finalActions]

/-- Every implicit table is the erasure of an explicit table whose final
    action is the conventional 1RZ. The choice of this action is immaterial
    for the step-count variant BB_S(6), but matters for tape-1 counts. -/
def embedImplicit (m : Machine) : ExplicitMachine := fun slot =>
  match m slot with
  | some t => .go t
  | none => .stop ⟨true, true⟩

theorem erase_embed (m : Machine) : eraseFinal (embedImplicit m) = m := by
  funext slot
  cases h : m slot with
  | none => simp [eraseFinal, embedImplicit, h]
  | some t => simp [eraseFinal, embedImplicit, h]

/-- Certified universal coverage in the implicit semantics transfers to
    every explicit six-state table with any of the four final actions. -/
def ExplicitDecidedBelow (bound : Nat) (m : ExplicitMachine) : Prop :=
  ExplicitNeverHalts m ∨
    ∃ n, n+1 ≤ bound ∧ ExplicitHaltsAfter m n

theorem explicit_decision_iff (bound : Nat) (m : ExplicitMachine) :
    ExplicitDecidedBelow bound m ↔ DecidedBelow bound (eraseFinal m) := by
  unfold ExplicitDecidedBelow DecidedBelow
  simp only [explicit_never_iff_implicit, explicit_halts_iff_implicit]

theorem all_explicit_iff_all_implicit (bound : Nat) :
    (∀ m : ExplicitMachine, ExplicitDecidedBelow bound m) ↔
      (∀ m : Machine, DecidedBelow bound m) := by
  constructor
  · intro h m
    have hm := h (embedImplicit m)
    rwa [explicit_decision_iff, erase_embed] at hm
  · intro h m
    exact (explicit_decision_iff bound m).2 (h (eraseFinal m))

theorem explicit_coverage_if_cert (bound : Nat)
    (cert : Cover (DecidedBelow bound) emptyTable) :
    ∀ m : ExplicitMachine, ExplicitDecidedBelow bound m := by
  intro m
  exact (explicit_decision_iff bound m).2 (global_coverage cert (eraseFinal m))

#print axioms erase_embed
#print axioms explicit_decision_iff
#print axioms all_explicit_iff_all_implicit
#print axioms explicit_coverage_if_cert

#print axioms project_step
#print axioms project_run
#print axioms explicit_halts_iff_implicit
#print axioms explicit_never_iff_implicit
#print axioms four_final_actions
#print axioms each_final_action_listed
end BB6Coverage

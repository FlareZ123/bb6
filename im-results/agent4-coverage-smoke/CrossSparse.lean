import CrossUpper
import TreeCoverage

namespace BB6.CoverageAdapter

/-- Exact conversion of assigned and unassigned sparse transitions. -/
def instructionTo8 : BB6.Coverage.SimpleInstruction → BB6Coverage.Transition :=
  Option.map (fun (w, d, q) => ({write := w, right := d, next := q} : BB6Coverage.Move))

def instructionTo13 : BB6Coverage.Transition → BB6.Coverage.SimpleInstruction :=
  Option.map (fun t => (t.write, t.right, t.next))

@[simp] theorem instructionTo13_to8 (i : BB6.Coverage.SimpleInstruction) :
    instructionTo13 (instructionTo8 i) = i := by
  cases i with
  | none => rfl
  | some p => rcases p with ⟨w,d,q⟩; rfl

@[simp] theorem instructionTo8_to13 (i : BB6Coverage.Transition) :
    instructionTo8 (instructionTo13 i) = i := by
  cases i with
  | none => rfl
  | some p => cases p; rfl

def sparseTo8 (p : BB6.Coverage.PartialMachine) : BB6Coverage.PartialMachine :=
  fun s => (p s.1 s.2).map instructionTo8

def sparseTo13 (p : BB6Coverage.PartialMachine) : BB6.Coverage.PartialMachine :=
  fun q b => (p (q,b)).map instructionTo13

theorem sparseTo13_to8 (p : BB6.Coverage.PartialMachine) :
    sparseTo13 (sparseTo8 p) = p := by
  funext q b
  cases h : p q b with
  | none => simp [sparseTo13, sparseTo8, h]
  | some i => simp [sparseTo13, sparseTo8, h]

theorem sparseTo8_to13 (p : BB6Coverage.PartialMachine) :
    sparseTo8 (sparseTo13 p) = p := by
  funext slot
  cases h : p slot with
  | none => simp [sparseTo13, sparseTo8, h]
  | some i => simp [sparseTo13, sparseTo8, h]

/-- The corresponding sparse cylinders have exactly the same completions. -/
theorem sparse_compatibility_iff (p : BB6.Coverage.PartialMachine)
    (m : BB6.Coverage.SimpleMachine) :
    BB6Coverage.compatible (sparseTo8 p) (toAgent8Machine m) ↔
      BB6.Coverage.Extends p m := by
  constructor
  · intro h q b i hi
    have hs : sparseTo8 p (q,b) = some (instructionTo8 i) := by
      simp [sparseTo8, hi]
    have ht := h (q,b) (instructionTo8 i) hs
    have hi2 : instructionTo8 (m q b) = instructionTo8 i := by
      simpa only [toAgent8Machine, instructionTo8] using ht
    have hi3 := congrArg instructionTo13 hi2
    simpa using hi3
  · intro h slot t ht
    rcases slot with ⟨q,b⟩
    cases hp : p q b with
    | none => simp [sparseTo8, hp] at ht
    | some i =>
      have htEq : instructionTo8 i = t := by
        simpa [sparseTo8, hp] using ht
      rw [← htEq]
      simp only [toAgent8Machine, instructionTo8]
      rw [h q b i hp]

end BB6.CoverageAdapter

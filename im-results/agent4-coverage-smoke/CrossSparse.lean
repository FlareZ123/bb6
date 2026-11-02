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

end BB6.CoverageAdapter

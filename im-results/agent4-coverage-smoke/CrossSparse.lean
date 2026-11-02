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

end BB6.CoverageAdapter

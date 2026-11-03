import ZeroMaskOracle

namespace BB6Coverage

/-- Follow only known zero-writing read-zero instructions.  A repetition
    of a control state returns the finite set of visited states.  A missing,
    halting or positive-writing instruction rejects this particular method.
    The six-state limit is explicit; no unchecked cycle inference is used. -/
def collectZeroPath (p : PartialMachine)
    (visited : List (Fin 6)) (state : Fin 6) : Nat → Option (List (Fin 6))
  | 0 => if state ∈ visited then some visited else none
  | fuel+1 =>
    if state ∈ visited then some visited
    else
      match p (state, false) with
      | some (some mv) =>
        if mv.write then none
        else collectZeroPath p (state :: visited) mv.next fuel
      | _ => none

/-- Candidate mask discovery performs at most six original-table queries,
    and the original, source-certified 6-mask check then confirms it.
    No exhaustive 64-mask enumeration is needed for a successful witness. -/
def pathMaskCheck (p : PartialMachine) : Bool :=
  match collectZeroPath p [] 0 6 with
  | none => false
  | some visited => zeroMaskCheck p (fun s => decide (s ∈ visited))

/-- Source-connected all-time certificate: even if a path collector has a
    bug, accepting a mask must pass the existing independent closed-mask
    checker before the nonhalting proof is constructed. -/
theorem pathMaskCheck_sound (p : PartialMachine) (bound : Nat)
    (h : pathMaskCheck p = true) : Cover (DecidedBelow bound) p := by
  cases hv : collectZeroPath p [] 0 6 with
  | none =>
      simp [pathMaskCheck, hv] at h
  | some visited =>
      apply zeroMaskCheck_sound p (fun s => decide (s ∈ visited)) bound
      simpa [pathMaskCheck, hv] using h

theorem turningZeroWriterPathDemo : pathMaskCheck turningZeroWriter = true := by
  decide

#print axioms pathMaskCheck_sound
#print axioms turningZeroWriterPathDemo
end BB6Coverage

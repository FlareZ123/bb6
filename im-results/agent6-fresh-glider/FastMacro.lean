import MacroOracle
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- Each n has at most one candidate displacement, namely the actual
    finite-run head position. This removes the redundant displacement
    search from the first executable oracle. -/
def fastMacroRight (p : PartialMachine) (limit : Nat) : Bool :=
  (List.range limit).any (fun i =>
    match finitePartialRun p (i+1) finiteBlank with
    | none => false
    | some c =>
        if 0 < c.head then finiteMacroRightCheck p (i+1) c.head.toNat
        else false)

theorem fastMacroRight_sound (p : PartialMachine) (limit bound : Nat)
    (h : fastMacroRight p limit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  cases hc : finitePartialRun p (i+1) finiteBlank with
  | none =>
      simp [fastMacroRight, hc] at hi
  | some c =>
      by_cases hpos : 0 < c.head
      · have hcheck :
            finiteMacroRightCheck p (i+1) c.head.toNat = true := by
          simpa [fastMacroRight, hc, hpos] using hi
        exact finiteMacroRightCheck_sound p (i+1) c.head.toNat bound
          (by omega) (by omega) hcheck
      · simp [fastMacroRight, hc, hpos] at hi

def fastMacroLeft (p : PartialMachine) (limit : Nat) : Bool :=
  (List.range limit).any (fun i =>
    match finitePartialRun p (i+1) finiteBlank with
    | none => false
    | some c =>
        if c.head < 0 then finiteMacroLeftCheck p (i+1) (-c.head).toNat
        else false)

theorem fastMacroLeft_sound (p : PartialMachine) (limit bound : Nat)
    (h : fastMacroLeft p limit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  cases hc : finitePartialRun p (i+1) finiteBlank with
  | none =>
      simp [fastMacroLeft, hc] at hi
  | some c =>
      by_cases hneg : c.head < 0
      · have hcheck :
            finiteMacroLeftCheck p (i+1) (-c.head).toNat = true := by
          simpa [fastMacroLeft, hc, hneg] using hi
        exact finiteMacroLeftCheck_sound p (i+1) (-c.head).toNat bound
          (by omega) (by omega) hcheck
      · simp [fastMacroLeft, hc, hneg] at hi

/-- Dynamic bidirectional search uses only one candidate shift per
    successful finite prefix. -/
def fastMacroOracle (p : PartialMachine) (limit : Nat) : Bool :=
  fastMacroRight p limit || fastMacroLeft p limit

theorem fastMacroOracle_sound (p : PartialMachine) (limit bound : Nat)
    (h : fastMacroOracle p limit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hr | hl
  · exact fastMacroRight_sound p limit bound hr
  · exact fastMacroLeft_sound p limit bound hl

/-- Straightforward bounds-independent all-time certificate of five-step
    left-/right-frontier growth. -/
theorem five_fast_example : fastMacroRight fiveStepMacroTable 5 = true := by
  decide

theorem left_fast_example : fastMacroLeft leftMacroExample 3 = true := by
  decide

#print axioms fastMacroRight_sound
#print axioms fastMacroLeft_sound
#print axioms fastMacroOracle_sound

end BB6Coverage

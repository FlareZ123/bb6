import ControlPathAudit

namespace BB6Coverage

/-- Globally enumerate the six read-zero rows in the original 25-choice
    machine space. Each branch is one real transition, not a guessed
    pruning condition. Each final sparse table leaves all read-one rows
    arbitrary and is certified only by an original-source oracle. -/
def zeroRowAudit : (rows : List (Fin 6)) → (p : PartialMachine) →
    (bound rayLimit : Nat) → FrontierAudit (DecidedBelow bound) p
  | [], p, bound, rayLimit =>
      if h : finiteDecisionOracle p bound rayLimit = true then
        .certified p (finiteDecisionOracle_sound p bound rayLimit h)
      else .unresolved p
  | row :: rest, p, bound, rayLimit =>
      if h : p (row, false) = none then
        .branch p (row, false) h
          (fun t _ => zeroRowAudit rest (refine p (row, false) t) bound rayLimit)
      else
        zeroRowAudit rest p bound rayLimit

/-- The entire raw six-state space with *every* read-zero input enumerated.
    At terminals only genuine fully demonstrated short halting or infinite
    fresh-ray / pristine-tape certificates are accepted; all others are
    left explicitly open. The executable report is enormous and is not
    evaluated by the Lean kernel here. -/
def globalZeroRowAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  zeroRowAudit (List.finRange 6) emptyTable 6 6

theorem globalZeroRowAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalZeroRowAudit.open m :=
  globalZeroRowAudit.exhaustive m (empty_compatible m)

theorem globalZeroRowAudit_conserves :
    globalZeroRowAudit.report.1 + globalZeroRowAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalZeroRowAudit.report_conserves
    _ = 25^12 := by decide

#print axioms globalZeroRowAudit_exhaustive
#print axioms globalZeroRowAudit_conserves

end BB6Coverage

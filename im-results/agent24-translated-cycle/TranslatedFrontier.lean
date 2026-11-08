import TranslatedFiniteOracle
import LassoTraceAudit

namespace BB6Coverage

/-- Search every entry prefix up to an inclusive bound and every positive
    translated-cycle length up to an inclusive bound. -/
def finiteTranslatedOracle (p : PartialMachine)
    (entryLimit periodLimit : Nat) : Bool :=
  (List.range (entryLimit + 1)).any (fun entry =>
    (List.range periodLimit).any (fun j =>
      finiteTranslatedCheck p entry (j+1)))

theorem finiteTranslatedOracle_sound (p : PartialMachine)
    (entryLimit periodLimit bound : Nat)
    (h : finiteTranslatedOracle p entryLimit periodLimit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨entry, _, he⟩ := List.any_eq_true.mp h
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp he
  exact finiteTranslatedCheck_sound p entry (j+1) bound (by omega) hj

/-- Adds the translated-cycle certificate to the previous sound decision
    oracle without changing any existing halt or nonhalt interpretations. -/
def translatedDecisionOracle (p : PartialMachine)
    (bound rayLimit lassoLimit entryLimit macroLimit transEntry transPeriod : Nat) : Bool :=
  lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit ||
    finiteTranslatedOracle p transEntry transPeriod

theorem translatedDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit lassoLimit entryLimit macroLimit transEntry transPeriod : Nat)
    (h : translatedDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit
      transEntry transPeriod = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hprior | hnew
  · exact lassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit hprior
  · exact finiteTranslatedOracle_sound p transEntry transPeriod bound hnew

/-- Certificate discovery branches on the next physically consulted unknown
    instruction; every unclassified subtree remains explicitly open. -/
def translatedPhysicalTraceAudit (p : PartialMachine)
    (bound rayLimit scanLimit lassoLimit entryLimit macroLimit
      transEntry transPeriod : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
    if h : translatedDecisionOracle p bound rayLimit lassoLimit entryLimit
        macroLimit transEntry transPeriod = true then
      .certified p (translatedDecisionOracle_sound p bound rayLimit lassoLimit
        entryLimit macroLimit transEntry transPeriod h)
    else .unresolved p
  | depth + 1 =>
    if h : translatedDecisionOracle p bound rayLimit lassoLimit entryLimit
        macroLimit transEntry transPeriod = true then
      .certified p (translatedDecisionOracle_sound p bound rayLimit lassoLimit
        entryLimit macroLimit transEntry transPeriod h)
    else
      match hs : firstUnknownPhysical p scanLimit finiteBlank with
      | none => .unresolved p
      | some slot =>
        .branch p slot (firstUnknownPhysical_sound p scanLimit finiteBlank slot hs)
          (fun t _ => translatedPhysicalTraceAudit (refine p slot t)
            bound rayLimit scanLimit lassoLimit entryLimit macroLimit
            transEntry transPeriod depth)

def globalTranslatedPhysicalTraceAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  translatedPhysicalTraceAudit emptyTable 6 6 12 12 12 12 12 12 4

theorem globalTranslatedPhysicalTraceAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalTranslatedPhysicalTraceAudit.open m :=
  globalTranslatedPhysicalTraceAudit.exhaustive m (empty_compatible m)

theorem globalTranslatedPhysicalTraceAudit_conserves :
    globalTranslatedPhysicalTraceAudit.report.1 +
      globalTranslatedPhysicalTraceAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalTranslatedPhysicalTraceAudit.report_conserves
    _ = 25^12 := by decide

/-- The new decision oracle strictly extends the previous sufficient
    predicate at a seven-entry translating marker cylinder. -/
theorem movingPair_new_decision :
    translatedDecisionOracle movingPairTable 6 12 12 12 12 12 12 = true := by
  have h : finiteTranslatedOracle movingPairTable 12 12 = true := by
    apply List.any_eq_true.mpr
    refine ⟨2, by decide, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨4, by decide, movingPair_check⟩
  simp [translatedDecisionOracle, h]

#print axioms finiteTranslatedOracle_sound
#print axioms translatedDecisionOracle_sound
#print axioms globalTranslatedPhysicalTraceAudit_exhaustive
#print axioms globalTranslatedPhysicalTraceAudit_conserves
#print axioms movingPair_new_decision
end BB6Coverage

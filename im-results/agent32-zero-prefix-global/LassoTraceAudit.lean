import FiniteLassoOracle
import EntryMacroLeft

namespace BB6Coverage

def lassoDecisionOracle (p : PartialMachine)
    (bound rayLimit lassoLimit entryLimit macroLimit : Nat) : Bool :=
  (finiteDecisionOracle p bound rayLimit || finiteLassoOracle p lassoLimit) ||
    finiteEntryMacroBiOracle p entryLimit macroLimit

theorem lassoDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit lassoLimit entryLimit macroLimit : Nat)
    (h : lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  have hor :
      (finiteDecisionOracle p bound rayLimit = true ∨
        finiteLassoOracle p lassoLimit = true) ∨
      finiteEntryMacroBiOracle p entryLimit macroLimit = true := by
    simpa only [lassoDecisionOracle, Bool.or_eq_true] using h
  rcases hor with hbase | hentry
  · rcases hbase with hdecision | hlasso
    · exact finiteDecisionOracle_sound p bound rayLimit hdecision
    · exact finiteLassoOracle_sound p lassoLimit bound hlasso
  · exact finiteEntryMacroBiOracle_sound p entryLimit macroLimit bound hentry

def lassoPhysicalTraceAudit (p : PartialMachine)
    (bound rayLimit scanLimit lassoLimit entryLimit macroLimit : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true then
        .certified p (lassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit h)
      else .unresolved p
  | depth+1 =>
      if h : lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true then
        .certified p (lassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit h)
      else
        match hs : firstUnknownPhysical p scanLimit finiteBlank with
        | none => .unresolved p
        | some slot =>
            .branch p slot
              (firstUnknownPhysical_sound p scanLimit finiteBlank slot hs)
              (fun t _ => lassoPhysicalTraceAudit
                (refine p slot t) bound rayLimit scanLimit lassoLimit entryLimit macroLimit depth)

def globalLassoPhysicalTraceAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 12

theorem globalLassoPhysicalTraceAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalLassoPhysicalTraceAudit.open m :=
  globalLassoPhysicalTraceAudit.exhaustive m (empty_compatible m)

theorem globalLassoPhysicalTraceAudit_conserves :
    globalLassoPhysicalTraceAudit.report.1 +
      globalLassoPhysicalTraceAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable :=
      globalLassoPhysicalTraceAudit.report_conserves
    _ = 25^12 := by decide

theorem readOneLasso_new_oracle_accepts :
    lassoDecisionOracle readOneLassoTable 6 6 12 2 4 = true := by
  decide

theorem entryToBExample_new_oracle_accepts :
    lassoDecisionOracle entryToBExample 6 6 12 2 4 = true := by
  have he : finiteEntryMacroOracle entryToBExample 2 4 = true := by
    apply List.any_eq_true.mpr
    refine ⟨1, by decide, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨2, by decide, entryToB_check⟩
  simp [lassoDecisionOracle, finiteEntryMacroBiOracle, he]


#print axioms lassoDecisionOracle_sound
#print axioms entryToBExample_new_oracle_accepts
#print axioms globalLassoPhysicalTraceAudit_exhaustive
#print axioms globalLassoPhysicalTraceAudit_conserves

end BB6Coverage

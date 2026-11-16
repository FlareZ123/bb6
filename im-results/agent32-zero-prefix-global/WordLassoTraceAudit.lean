import LassoTraceAudit
import WordMirror

namespace BB6Coverage

/-- Add the source-sound finite-word translated-tail certificate to the
    physical lasso/entry-macro decision oracle. The word may contain any
    finite set of marks to the right of the genuine blank-root entry. -/
def wordLassoDecisionOracle (p : PartialMachine)
    (bound rayLimit lassoLimit entryLimit macroLimit : Nat) : Bool :=
  lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit ||
    finiteWordBiOracle p entryLimit macroLimit

theorem wordLassoDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit lassoLimit entryLimit macroLimit : Nat)
    (h : wordLassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  have hor :
      lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true ∨
        finiteWordBiOracle p entryLimit macroLimit = true := by
    simpa [wordLassoDecisionOracle, Bool.or_eq_true] using h
  rcases hor with hlasso | hword
  · exact lassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit hlasso
  · exact finiteWordBiOracle_sound p entryLimit macroLimit bound hword

/-- The existing physical first-unknown branching policy, augmented by
    exact finite-word recurrence on either side of the actual tape. -/
def wordLassoPhysicalTraceAudit (p : PartialMachine)
    (bound rayLimit scanLimit lassoLimit entryLimit macroLimit : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : wordLassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true then
        .certified p
          (wordLassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit h)
      else .unresolved p
  | depth+1 =>
      if h : wordLassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true then
        .certified p
          (wordLassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit h)
      else
        match hs : firstUnknownPhysical p scanLimit finiteBlank with
        | none => .unresolved p
        | some slot =>
            .branch p slot
              (firstUnknownPhysical_sound p scanLimit finiteBlank slot hs)
              (fun t _ => wordLassoPhysicalTraceAudit
                (refine p slot t) bound rayLimit scanLimit lassoLimit entryLimit macroLimit depth)

/-- A globally exhaustive-or-open raw-table tree with the finite-word
    oracle enabled. The depth-four report is evaluated separately. -/
def globalWordLassoPhysicalTraceAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  wordLassoPhysicalTraceAudit emptyTable 6 6 12 12 3 4 12

theorem globalWordLassoPhysicalTraceAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalWordLassoPhysicalTraceAudit.open m :=
  globalWordLassoPhysicalTraceAudit.exhaustive m (empty_compatible m)

theorem globalWordLassoPhysicalTraceAudit_conserves :
    globalWordLassoPhysicalTraceAudit.report.1 +
      globalWordLassoPhysicalTraceAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable :=
      globalWordLassoPhysicalTraceAudit.report_conserves
    _ = 25^12 := by decide

/-- Regression: the word oracle finds a two-mark translated tail that the
    single-marker oracle rejects at the same small entry/macro bounds. -/
theorem wordLassoDecisionOracle_accepts_twoMark :
    wordLassoDecisionOracle twoMarkWordPump 6 6 12 12 3 4 = true := by
  have hentry : finiteWordEntryOracle twoMarkWordPump 3 4 = true := by
    apply List.any_eq_true.mpr
    refine ⟨2, by decide, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨2, by decide, twoMark_word_check⟩
  have hword : finiteWordBiOracle twoMarkWordPump 3 4 = true := by
    simp [finiteWordBiOracle, hentry]
  simp [wordLassoDecisionOracle, hword]

#print axioms wordLassoDecisionOracle_sound
#print axioms globalWordLassoPhysicalTraceAudit_exhaustive
#print axioms globalWordLassoPhysicalTraceAudit_conserves
#print axioms wordLassoDecisionOracle_accepts_twoMark

end BB6Coverage

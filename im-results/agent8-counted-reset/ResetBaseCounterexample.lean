import ChampionRootBridge

/-!
# Finite counterexamples to the retired reset-base trace family

The proposed `CountedResetBase` endpoints do not match the canonical
`tm2` table.  These are exact `fRun` computations, not an inference from
a simulator with set-valued tape storage: the marked-cell lists below use
the same prepend/filter order as `FConfig.fMove`.
-/

namespace BB6Coverage.Agent8ResetBaseCounterexample

open BB6Coverage.Agent48Champion

def proposedInput0 : FConfig :=
  ⟨3,0,[-7,-4,-1,2,3,4,7,8,9]⟩

def proposedInput1 : FConfig :=
  ⟨3,0,[-8,-5,-2,0,2,3,4,7,8,9]⟩

def proposedInput2 : FConfig :=
  ⟨3,0,[-6,-3,-1,0,2,3,4,7,8,9]⟩

def proposedOutput0 : FConfig :=
  ⟨3,5,[-7,-6,-5,-4,-1,1,2,3,4,5,7,8,9,12,13,14]⟩

def proposedOutput1 : FConfig :=
  ⟨3,5,[-8,-7,-6,-5,-2,0,1,2,3,4,5,7,8,9,12,13,14]⟩

def proposedOutput2 : FConfig :=
  ⟨3,5,[-8,-7,-6,-3,-1,0,1,2,3,4,5,7,8,9,12,13,14]⟩

/-- Actual finite-list output for the proposed marker-zero input. -/
def actualOutput0 : FConfig :=
  ⟨3,27,
    [27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,
      1,0,-1,-7,-4]⟩

/-- Actual finite-list output for the proposed marker-one input. -/
def actualOutput1 : FConfig :=
  ⟨1,29,
    [28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,
      6,5,4,3,2,1,0,-8,-5,-2]⟩

/-- Actual finite-list output for the proposed marker-two input. -/
def actualOutput2 : FConfig :=
  ⟨2,31,
    [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,
      6,5,4,3,2,1,0,-6,-3,-1]⟩

theorem actual_trace0 :
    fRun tm2 63 proposedInput0 = some actualOutput0 := by
  decide

theorem actual_trace1 :
    fRun tm2 67 proposedInput1 = some actualOutput1 := by
  decide

theorem actual_trace2 :
    fRun tm2 71 proposedInput2 = some actualOutput2 := by
  decide

/-- The advertised 63-step marker-zero endpoint is false. -/
theorem proposed_trace0_refuted :
    fRun tm2 63 proposedInput0 ≠ some proposedOutput0 := by
  rw [actual_trace0]
  decide

/-- The advertised 67-step marker-one endpoint is false. -/
theorem proposed_trace1_refuted :
    fRun tm2 67 proposedInput1 ≠ some proposedOutput1 := by
  rw [actual_trace1]
  decide

/-- The advertised 71-step marker-two endpoint is false. -/
theorem proposed_trace2_refuted :
    fRun tm2 71 proposedInput2 ≠ some proposedOutput2 := by
  rw [actual_trace2]
  decide

#print axioms actual_trace0
#print axioms actual_trace1
#print axioms actual_trace2
#print axioms proposed_trace0_refuted
#print axioms proposed_trace1_refuted
#print axioms proposed_trace2_refuted

end BB6Coverage.Agent8ResetBaseCounterexample

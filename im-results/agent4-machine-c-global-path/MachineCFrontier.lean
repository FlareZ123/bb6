import MachineCPath
import LassoTraceAudit

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- The exact physical successor slots for Machine C's first four
    successful global proof-tree splits. All are source-valid reads,
    rather than an enumeration of hypothetical all-zero control paths. -/
theorem machineC_first_four_global_slots :
    ((List.range 4).map (fun n =>
      firstUnknownPhysical (machineCPrefix n) 12 finiteBlank)) =
      (machineCVisited.take 4).map some := by decide

/-- The source-sound finite-halt, fresh-ray, exact-lasso, and short
    finite-entry macro oracles all decline this particular root path,
    at the exact four-level audit settings used by Agent32. -/
theorem machineC_oracle_false_first_five :
    (List.range 5).map (fun n =>
      lassoDecisionOracle (machineCPrefix n) 6 6 12 2 4) =
        List.replicate 5 false := by decide

private theorem open_lasso_step (p : PartialMachine) (d : Nat)
    (slot : Slot)
    (hf : lassoDecisionOracle p 6 6 12 2 4 = false)
    (hs : firstUnknownPhysical p 12 finiteBlank = some slot) :
    (lassoPhysicalTraceAudit p 6 6 12 12 2 4 (d+1)).open machineC ↔
      (lassoPhysicalTraceAudit
        (refine p slot (machineC slot)) 6 6 12 12 2 4 d).open machineC := by
  have hn : ¬ lassoDecisionOracle p 6 6 12 2 4 = true := by simp [hf]
  rw [lassoPhysicalTraceAudit.eq_2]
  split
  · rename_i hhit
    exact False.elim (hn hhit)
  · split
    · rename_i hnone
      cases hnone.symm.trans hs
    · rename_i found hfound
      have heq : found = slot := by simpa [hfound] using hs
      subst found
      rfl

/-- Four real consulted slots route the original Machine C through the
    original global adaptive lasso/macro decision tree into a genuine
    unresolved leaf. The lemma is not a halting classification. -/
theorem machineC_depth_four_open :
    (lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4).open
      machineC := by
  let s0 : Slot := (⟨0, by decide⟩, false)
  let s1 : Slot := (⟨1, by decide⟩, false)
  let s2 : Slot := (⟨2, by decide⟩, true)
  let s3 : Slot := (⟨2, by decide⟩, false)
  let p0 : PartialMachine := emptyTable
  let p1 : PartialMachine := refine p0 s0 (machineC s0)
  let p2 : PartialMachine := refine p1 s1 (machineC s1)
  let p3 : PartialMachine := refine p2 s2 (machineC s2)
  let p4 : PartialMachine := refine p3 s3 (machineC s3)
  have f0 : lassoDecisionOracle p0 6 6 12 2 4 = false := by decide
  have f1 : lassoDecisionOracle p1 6 6 12 2 4 = false := by decide
  have f2 : lassoDecisionOracle p2 6 6 12 2 4 = false := by decide
  have f3 : lassoDecisionOracle p3 6 6 12 2 4 = false := by decide
  have f4 : lassoDecisionOracle p4 6 6 12 2 4 = false := by decide
  have h0 : firstUnknownPhysical p0 12 finiteBlank = some s0 := by decide
  have h1 : firstUnknownPhysical p1 12 finiteBlank = some s1 := by decide
  have h2 : firstUnknownPhysical p2 12 finiteBlank = some s2 := by decide
  have h3 : firstUnknownPhysical p3 12 finiteBlank = some s3 := by decide
  have e4 : (lassoPhysicalTraceAudit p4 6 6 12 12 2 4 0).open machineC := by
    simp [lassoPhysicalTraceAudit, FrontierAudit.open, f4]
  have e3 : (lassoPhysicalTraceAudit p3 6 6 12 12 2 4 1).open machineC :=
    (open_lasso_step p3 0 s3 f3 h3).mpr e4
  have e2 : (lassoPhysicalTraceAudit p2 6 6 12 12 2 4 2).open machineC :=
    (open_lasso_step p2 1 s2 f2 h2).mpr e3
  have e1 : (lassoPhysicalTraceAudit p1 6 6 12 12 2 4 3).open machineC :=
    (open_lasso_step p1 2 s1 f1 h1).mpr e2
  have e0 : (lassoPhysicalTraceAudit p0 6 6 12 12 2 4 4).open machineC :=
    (open_lasso_step p0 3 s0 f0 h0).mpr e1
  exact e0

/-- One specific four-row sparse cylinder, containing Machine C, has
    all remaining eight inputs free: 25^8 possible completions. This
    is the cylinder reached by the first four true physical splits. -/
theorem machineC_first_four_mass :
    cylinderMass (machineCPrefix 4) = 25^8 := by decide

#print axioms machineC_first_four_global_slots
#print axioms machineC_oracle_false_first_five
#print axioms machineC_depth_four_open
#print axioms machineC_first_four_mass

end BB6Coverage

import Machine623Frontier

namespace BB6Coverage

set_option maxRecDepth 15000
set_option maxHeartbeats 0

/-- Verified one-step descent through the original sound partial machine
    audit, preserving the machine's true physical read slot. -/
private theorem open_lasso_step_deep (p : PartialMachine) (d : Nat)
    (slot : Slot)
    (hf : lassoDecisionOracle p 6 6 12 2 4 = false)
    (hs : firstUnknownPhysical p 96 finiteBlank = some slot) :
    (lassoPhysicalTraceAudit p 6 6 96 12 2 4 (d+1)).open machine623 ↔
      (lassoPhysicalTraceAudit
        (refine p slot (machine623 slot)) 6 6 96 12 2 4 d).open machine623 := by
  have hn : ¬ lassoDecisionOracle p 6 6 12 2 4 = true := by simp [hf]
  simp only [lassoPhysicalTraceAudit, dif_neg hn]
  split
  · rename_i hnone
    simp [hnone] at hs
  · rename_i actual hsome
    have heq : actual = slot :=
      Option.some.inj (hsome.symm.trans hs)
    subst actual
    rfl

/-- All twelve exact sparse prefixes of this authentic root evade the
    indicated bounded proof oracles. This is a property of the *oracle*,
    never a conclusion about actual eventual halting. -/
theorem machine623_oracles_false_all_prefixes :
    (List.range 12).map (fun n =>
      lassoDecisionOracle (machine623Prefix n) 6 6 12 2 4) =
        List.replicate 12 false := by decide

/-- All eleven physical first-unknown slots remain exactly trace-valid
    when scanned through the 54th primitive move. -/
theorem machine623_first_slots_scan96 :
    ((List.range 11).map (fun n =>
      firstUnknownPhysical (machine623Prefix n) 96 finiteBlank)) =
      machine623Visited.map some := machine623_first_slots

/-- At depth eleven the actual historical root is still an explicitly
    unresolved leaf of the same source-certified global branching audit.
    Unlike finite halting tests, this preserves all 25 possible transitions
    of every unassigned row in other parts of the global tree. -/
theorem machine623_depth_eleven_open :
    (lassoPhysicalTraceAudit emptyTable 6 6 96 12 2 4 11).open
      machine623 := by
  let s0 : Slot := (⟨0, by decide⟩, false)
  let s1 : Slot := (⟨1, by decide⟩, false)
  let s2 : Slot := (⟨2, by decide⟩, false)
  let s3 : Slot := (⟨3, by decide⟩, false)
  let s4 : Slot := (⟨3, by decide⟩, true)
  let s5 : Slot := (⟨2, by decide⟩, true)
  let s6 : Slot := (⟨1, by decide⟩, true)
  let s7 : Slot := (⟨0, by decide⟩, true)
  let s8 : Slot := (⟨4, by decide⟩, true)
  let s9 : Slot := (⟨4, by decide⟩, false)
  let s10 : Slot := (⟨5, by decide⟩, true)
  let p0 : PartialMachine := emptyTable
  let p1 : PartialMachine := refine p0 s0 (machine623 s0)
  let p2 : PartialMachine := refine p1 s1 (machine623 s1)
  let p3 : PartialMachine := refine p2 s2 (machine623 s2)
  let p4 : PartialMachine := refine p3 s3 (machine623 s3)
  let p5 : PartialMachine := refine p4 s4 (machine623 s4)
  let p6 : PartialMachine := refine p5 s5 (machine623 s5)
  let p7 : PartialMachine := refine p6 s6 (machine623 s6)
  let p8 : PartialMachine := refine p7 s7 (machine623 s7)
  let p9 : PartialMachine := refine p8 s8 (machine623 s8)
  let p10 : PartialMachine := refine p9 s9 (machine623 s9)
  let p11 : PartialMachine := refine p10 s10 (machine623 s10)
  have f0 : lassoDecisionOracle p0 6 6 12 2 4 = false := by decide
  have f1 : lassoDecisionOracle p1 6 6 12 2 4 = false := by decide
  have f2 : lassoDecisionOracle p2 6 6 12 2 4 = false := by decide
  have f3 : lassoDecisionOracle p3 6 6 12 2 4 = false := by decide
  have f4 : lassoDecisionOracle p4 6 6 12 2 4 = false := by decide
  have f5 : lassoDecisionOracle p5 6 6 12 2 4 = false := by decide
  have f6 : lassoDecisionOracle p6 6 6 12 2 4 = false := by decide
  have f7 : lassoDecisionOracle p7 6 6 12 2 4 = false := by decide
  have f8 : lassoDecisionOracle p8 6 6 12 2 4 = false := by decide
  have f9 : lassoDecisionOracle p9 6 6 12 2 4 = false := by decide
  have f10 : lassoDecisionOracle p10 6 6 12 2 4 = false := by decide
  have f11 : lassoDecisionOracle p11 6 6 12 2 4 = false := by decide
  have h0 : firstUnknownPhysical p0 96 finiteBlank = some s0 := by decide
  have h1 : firstUnknownPhysical p1 96 finiteBlank = some s1 := by decide
  have h2 : firstUnknownPhysical p2 96 finiteBlank = some s2 := by decide
  have h3 : firstUnknownPhysical p3 96 finiteBlank = some s3 := by decide
  have h4 : firstUnknownPhysical p4 96 finiteBlank = some s4 := by decide
  have h5 : firstUnknownPhysical p5 96 finiteBlank = some s5 := by decide
  have h6 : firstUnknownPhysical p6 96 finiteBlank = some s6 := by decide
  have h7 : firstUnknownPhysical p7 96 finiteBlank = some s7 := by decide
  have h8 : firstUnknownPhysical p8 96 finiteBlank = some s8 := by decide
  have h9 : firstUnknownPhysical p9 96 finiteBlank = some s9 := by decide
  have h10 : firstUnknownPhysical p10 96 finiteBlank = some s10 := by decide
  have e11 : (lassoPhysicalTraceAudit p11 6 6 96 12 2 4 0).open machine623 := by
    simp [lassoPhysicalTraceAudit, FrontierAudit.open, f11]
  have e10 : (lassoPhysicalTraceAudit p10 6 6 96 12 2 4 1).open machine623 :=
    (open_lasso_step_deep p10 0 s10 f10 h10).mpr e11
  have e9 : (lassoPhysicalTraceAudit p9 6 6 96 12 2 4 2).open machine623 :=
    (open_lasso_step_deep p9 1 s9 f9 h9).mpr e10
  have e8 : (lassoPhysicalTraceAudit p8 6 6 96 12 2 4 3).open machine623 :=
    (open_lasso_step_deep p8 2 s8 f8 h8).mpr e9
  have e7 : (lassoPhysicalTraceAudit p7 6 6 96 12 2 4 4).open machine623 :=
    (open_lasso_step_deep p7 3 s7 f7 h7).mpr e8
  have e6 : (lassoPhysicalTraceAudit p6 6 6 96 12 2 4 5).open machine623 :=
    (open_lasso_step_deep p6 4 s6 f6 h6).mpr e7
  have e5 : (lassoPhysicalTraceAudit p5 6 6 96 12 2 4 6).open machine623 :=
    (open_lasso_step_deep p5 5 s5 f5 h5).mpr e6
  have e4 : (lassoPhysicalTraceAudit p4 6 6 96 12 2 4 7).open machine623 :=
    (open_lasso_step_deep p4 6 s4 f4 h4).mpr e5
  have e3 : (lassoPhysicalTraceAudit p3 6 6 96 12 2 4 8).open machine623 :=
    (open_lasso_step_deep p3 7 s3 f3 h3).mpr e4
  have e2 : (lassoPhysicalTraceAudit p2 6 6 96 12 2 4 9).open machine623 :=
    (open_lasso_step_deep p2 8 s2 f2 h2).mpr e3
  have e1 : (lassoPhysicalTraceAudit p1 6 6 96 12 2 4 10).open machine623 :=
    (open_lasso_step_deep p1 9 s1 f1 h1).mpr e2
  have e0 : (lassoPhysicalTraceAudit p0 6 6 96 12 2 4 11).open machine623 :=
    (open_lasso_step_deep p0 10 s0 f0 h0).mpr e1
  exact e0

/-- Exactly one unknown row remains after the eleven exact physical splits. -/
theorem machine623_deep_leaf_mass :
    cylinderMass (machine623Prefix 11) = 25 := machine623_prefix_mass

#print axioms machine623_oracles_false_all_prefixes
#print axioms machine623_depth_eleven_open
#print axioms machine623_deep_leaf_mass

end BB6Coverage


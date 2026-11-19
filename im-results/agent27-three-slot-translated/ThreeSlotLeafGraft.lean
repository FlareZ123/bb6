import ResidualFrontierManifest
import IncrementalAudit
import TranslatedThreeSlot

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage

/-- The three-slot table is the depth-four physical leaf reached by
    A/0, B/0, A/1. -/

theorem agent27ThreeP0_old_oracle_false :
    lassoDecisionOracle agent27ThreeP0 6 6 12 2 4 = false := by decide
theorem agent27ThreeP1_old_oracle_false :
    lassoDecisionOracle agent27ThreeP1 6 6 12 2 4 = false := by decide
theorem agent27ThreeP2_old_oracle_false :
    lassoDecisionOracle agent27ThreeP2 6 6 12 2 4 = false := by decide
theorem agent27ThreeP3_old_oracle_false :
    lassoDecisionOracle agent27ThreeP3 6 6 12 2 4 = false := by decide

theorem agent27ThreeP0_next :
    firstUnknownPhysical agent27ThreeP0 12 finiteBlank =
      some agent27ThreeA0 := by decide
theorem agent27ThreeP1_next :
    firstUnknownPhysical agent27ThreeP1 12 finiteBlank =
      some agent27ThreeB0 := by decide
theorem agent27ThreeP2_next :
    firstUnknownPhysical agent27ThreeP2 12 finiteBlank =
      some agent27ThreeA1 := by decide
theorem agent27ThreeP3_no_unknown :
    firstUnknownPhysical agent27ThreeP3 12 finiteBlank = none := by decide

private theorem agent27Three_lasso_open_step
    (p : PartialMachine) (d : Nat) (slot : Slot)
    (hf : lassoDecisionOracle p 6 6 12 2 4 = false)
    (hs : firstUnknownPhysical p 12 finiteBlank = some slot)
    (m : Machine) :
    (lassoPhysicalTraceAudit p 6 6 12 12 2 4 (d+1)).open m ↔
      (lassoPhysicalTraceAudit (refine p slot (m slot))
        6 6 12 12 2 4 d).open m := by
  have hn : ¬ lassoDecisionOracle p 6 6 12 2 4 = true := by
    simp [hf]
  simp only [lassoPhysicalTraceAudit, dif_neg hn]
  split
  · rename_i hnone
    simp [hnone] at hs
  · rename_i actual hsome
    have heq : actual = slot := Option.some.inj (hsome.symm.trans hs)
    subst actual
    rfl

/-- Every completion of the three-slot cylinder is open in the old
    depth-four physical frontier. -/
theorem agent27ThreeParent_open_all (m : Machine)
    (hm : compatible agent27ThreeP3 m) :
    depth4ResidualAudit.open m := by
  have hA : m agent27ThreeA0 = agent27ThreeA0Action :=
    hm agent27ThreeA0 agent27ThreeA0Action (by decide)
  have hB : m agent27ThreeB0 = agent27ThreeB0Action :=
    hm agent27ThreeB0 agent27ThreeB0Action (by decide)
  have hA1 : m agent27ThreeA1 = agent27ThreeA1Action :=
    hm agent27ThreeA1 agent27ThreeA1Action (by decide)
  have h3 :
      (lassoPhysicalTraceAudit agent27ThreeP3 6 6 12 12 2 4 1).open m := by
    simp [lassoPhysicalTraceAudit, agent27ThreeP3_old_oracle_false,
      agent27ThreeP3_no_unknown]
  have h2 :
      (lassoPhysicalTraceAudit agent27ThreeP2 6 6 12 12 2 4 2).open m := by
    apply (agent27Three_lasso_open_step agent27ThreeP2 1 agent27ThreeA1
      agent27ThreeP2_old_oracle_false agent27ThreeP2_next m).2
    simpa [agent27ThreeP3, hA1] using h3
  have h1 :
      (lassoPhysicalTraceAudit agent27ThreeP1 6 6 12 12 2 4 3).open m := by
    apply (agent27Three_lasso_open_step agent27ThreeP1 2 agent27ThreeB0
      agent27ThreeP1_old_oracle_false agent27ThreeP1_next m).2
    simpa [agent27ThreeP2, hB] using h2
  have h0 :
      (lassoPhysicalTraceAudit agent27ThreeP0 6 6 12 12 2 4 4).open m := by
    apply (agent27Three_lasso_open_step agent27ThreeP0 3 agent27ThreeA0
      agent27ThreeP0_old_oracle_false agent27ThreeP0_next m).2
    simpa [agent27ThreeP1, hA] using h1
  simpa [depth4ResidualAudit, agent27ThreeP0] using h0

noncomputable def agent27ThreeGraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate depth4ResidualAudit agent27ThreeP3
    (agent27Three_cover 6)

/-- Exact open-set semantics for the global graft. -/
theorem agent27ThreeGraftedAudit_open_iff (m : Machine) :
    agent27ThreeGraftedAudit.open m ↔
      depth4ResidualAudit.open m ∧
        ¬ compatible agent27ThreeP3 m := by
  simpa [agent27ThreeGraftedAudit] using
    (addCertificate_open_iff depth4ResidualAudit agent27ThreeP3
      (agent27Three_cover 6) m (empty_compatible m))

/-- The entire three-slot parent is removed from the old open frontier. -/
theorem agent27Three_parent_closed_after_graft (m : Machine)
    (hm : compatible agent27ThreeP3 m) :
    ¬ agent27ThreeGraftedAudit.open m := by
  intro hopen
  have hpair := (agent27ThreeGraftedAudit_open_iff m).mp hopen
  exact hpair.2 hm

theorem agent27Three_leaf_closed (m : Machine)
    (hm : compatible agent27ThreeP3 m) :
    depth4ResidualAudit.open m ∧
      ¬ agent27ThreeGraftedAudit.open m := by
  exact ⟨agent27ThreeParent_open_all m hm,
    agent27Three_parent_closed_after_graft m hm⟩

theorem agent27ThreeGraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ agent27ThreeGraftedAudit.open m :=
  agent27ThreeGraftedAudit.exhaustive m (empty_compatible m)

theorem agent27ThreeGraftedAudit_conserves :
    agent27ThreeGraftedAudit.report.1 +
      agent27ThreeGraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable :=
      agent27ThreeGraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms agent27ThreeP0_old_oracle_false
#print axioms agent27ThreeP1_old_oracle_false
#print axioms agent27ThreeP2_old_oracle_false
#print axioms agent27ThreeP3_old_oracle_false
#print axioms agent27ThreeP0_next
#print axioms agent27ThreeP1_next
#print axioms agent27ThreeP2_next
#print axioms agent27ThreeP3_no_unknown
#print axioms agent27ThreeParent_open_all
#print axioms agent27ThreeGraftedAudit_open_iff
#print axioms agent27Three_parent_closed_after_graft
#print axioms agent27Three_leaf_closed
#print axioms agent27ThreeGraftedAudit_exhaustive
#print axioms agent27ThreeGraftedAudit_conserves

end BB6Coverage

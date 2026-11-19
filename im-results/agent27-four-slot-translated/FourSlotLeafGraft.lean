import ResidualFrontierManifest
import IncrementalAudit
import TranslatedFourSlot

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage

/-- The four-slot translated cylinder is exactly the depth-four physical
    leaf reached by A/0, B/0, C/1, D/1. -/

theorem agent27FourP0_old_oracle_false :
    lassoDecisionOracle agent27FourP0 6 6 12 2 4 = false := by decide
theorem agent27FourP1_old_oracle_false :
    lassoDecisionOracle agent27FourP1 6 6 12 2 4 = false := by decide
theorem agent27FourP2_old_oracle_false :
    lassoDecisionOracle agent27FourP2 6 6 12 2 4 = false := by decide
theorem agent27FourP3_old_oracle_false :
    lassoDecisionOracle agent27FourP3 6 6 12 2 4 = false := by decide
theorem agent27FourP4_old_oracle_false :
    lassoDecisionOracle agent27FourP4 6 6 12 2 4 = false := by decide

theorem agent27FourP0_next :
    firstUnknownPhysical agent27FourP0 12 finiteBlank =
      some agent27FourA0 := by decide
theorem agent27FourP1_next :
    firstUnknownPhysical agent27FourP1 12 finiteBlank =
      some agent27FourB0 := by decide
theorem agent27FourP2_next :
    firstUnknownPhysical agent27FourP2 12 finiteBlank =
      some agent27FourC1 := by decide
theorem agent27FourP3_next :
    firstUnknownPhysical agent27FourP3 12 finiteBlank =
      some agent27FourD1 := by decide

/-- The 12-step physical scan stays inside the four assigned slots. -/
theorem agent27FourP4_no_unknown :
    firstUnknownPhysical agent27FourP4 12 finiteBlank = none := by decide

private theorem agent27Four_lasso_open_step
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

/-- Every completion of the four-slot cylinder is open in the existing
    depth-four physical frontier before the translated certificate is added. -/
theorem agent27FourParent_open_all (m : Machine)
    (hm : compatible agent27FourP4 m) :
    depth4ResidualAudit.open m := by
  have hA : m agent27FourA0 = agent27FourA0Action :=
    hm agent27FourA0 agent27FourA0Action (by decide)
  have hB : m agent27FourB0 = agent27FourB0Action :=
    hm agent27FourB0 agent27FourB0Action (by decide)
  have hC : m agent27FourC1 = agent27FourC1Action :=
    hm agent27FourC1 agent27FourC1Action (by decide)
  have hD : m agent27FourD1 = agent27FourD1Action :=
    hm agent27FourD1 agent27FourD1Action (by decide)
  have h4 :
      (lassoPhysicalTraceAudit agent27FourP4 6 6 12 12 2 4 0).open m := by
    simp [lassoPhysicalTraceAudit, agent27FourP4_old_oracle_false]
  have h3 :
      (lassoPhysicalTraceAudit agent27FourP3 6 6 12 12 2 4 1).open m := by
    apply (agent27Four_lasso_open_step agent27FourP3 0 agent27FourD1
      agent27FourP3_old_oracle_false agent27FourP3_next m).2
    simpa [agent27FourP4, hD] using h4
  have h2 :
      (lassoPhysicalTraceAudit agent27FourP2 6 6 12 12 2 4 2).open m := by
    apply (agent27Four_lasso_open_step agent27FourP2 1 agent27FourC1
      agent27FourP2_old_oracle_false agent27FourP2_next m).2
    simpa [agent27FourP3, hC] using h3
  have h1 :
      (lassoPhysicalTraceAudit agent27FourP1 6 6 12 12 2 4 3).open m := by
    apply (agent27Four_lasso_open_step agent27FourP1 2 agent27FourB0
      agent27FourP1_old_oracle_false agent27FourP1_next m).2
    simpa [agent27FourP2, hB] using h2
  have h0 :
      (lassoPhysicalTraceAudit agent27FourP0 6 6 12 12 2 4 4).open m := by
    apply (agent27Four_lasso_open_step agent27FourP0 3 agent27FourA0
      agent27FourP0_old_oracle_false agent27FourP0_next m).2
    simpa [agent27FourP1, hA] using h1
  simpa [depth4ResidualAudit, agent27FourP0] using h0

noncomputable def agent27FourGraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate depth4ResidualAudit agent27FourP4
    (agent27Four_cover 6)

/-- Exact open-set semantics: only completions of the four-slot source
    cylinder are removed from the old global open frontier. -/
theorem agent27FourGraftedAudit_open_iff (m : Machine) :
    agent27FourGraftedAudit.open m ↔
      depth4ResidualAudit.open m ∧
        ¬ compatible agent27FourP4 m := by
  simpa [agent27FourGraftedAudit] using
    (addCertificate_open_iff depth4ResidualAudit agent27FourP4
      (agent27Four_cover 6) m (empty_compatible m))

/-- The whole four-slot parent leaf is closed by the new certificate. -/
theorem agent27Four_parent_closed_after_graft (m : Machine)
    (hm : compatible agent27FourP4 m) :
    ¬ agent27FourGraftedAudit.open m := by
  intro hopen
  exact (agent27FourGraftedAudit_open_iff m).mp hopen |>.2 hm

theorem agent27Four_leaf_closed (m : Machine)
    (hm : compatible agent27FourP4 m) :
    depth4ResidualAudit.open m ∧
      ¬ agent27FourGraftedAudit.open m := by
  exact ⟨agent27FourParent_open_all m hm,
    agent27Four_parent_closed_after_graft m hm⟩

theorem agent27FourGraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ agent27FourGraftedAudit.open m :=
  agent27FourGraftedAudit.exhaustive m (empty_compatible m)

theorem agent27FourGraftedAudit_conserves :
    agent27FourGraftedAudit.report.1 +
      agent27FourGraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable :=
      agent27FourGraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms agent27FourP0_old_oracle_false
#print axioms agent27FourP1_old_oracle_false
#print axioms agent27FourP2_old_oracle_false
#print axioms agent27FourP3_old_oracle_false
#print axioms agent27FourP4_old_oracle_false
#print axioms agent27FourP0_next
#print axioms agent27FourP1_next
#print axioms agent27FourP2_next
#print axioms agent27FourP3_next
#print axioms agent27FourP4_no_unknown
#print axioms agent27FourParent_open_all
#print axioms agent27FourGraftedAudit_open_iff
#print axioms agent27Four_parent_closed_after_graft
#print axioms agent27Four_leaf_closed
#print axioms agent27FourGraftedAudit_exhaustive
#print axioms agent27FourGraftedAudit_conserves

end BB6Coverage

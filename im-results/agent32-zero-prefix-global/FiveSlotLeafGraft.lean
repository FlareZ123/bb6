import LassoTraceAudit
import IncrementalAudit
import TranslatedFiveSlot

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage

/-!
Integrate Agent 27's five-slot, source-certified translated finite-support
cylinder into the existing depth-four physical frontier.

`agent27Depth4Audit` is the exact expression used for `depth4ResidualAudit`
in `ResidualFrontierManifest.lean`: `lassoPhysicalTraceAudit emptyTable 6 6
12 12 2 4 4`.  We use the same physical audit directly, without importing
the manifest's unrelated terminal-list and mass-report machinery.

The four-slot parent is the exact A/0, B/0, C/1, D/1 path.  We prove
directly that every completion of this parent is open in the physical audit,
then use the generic exact open-set theorem for certificate grafts.  The
resulting theorem says that the graft removes precisely the five-slot
nonhalting cylinder from this parent and preserves every other open
completion.
-/

/-- Same physical audit expression as `depth4ResidualAudit` in
    `ResidualFrontierManifest.lean`. -/
def agent27Depth4Audit : FrontierAudit (DecidedBelow 6) emptyTable :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4

theorem agent27P0_old_oracle_false :
    lassoDecisionOracle agent27P0 6 6 12 2 4 = false := by decide
theorem agent27P1_old_oracle_false :
    lassoDecisionOracle agent27P1 6 6 12 2 4 = false := by decide
theorem agent27P2_old_oracle_false :
    lassoDecisionOracle agent27P2 6 6 12 2 4 = false := by decide
theorem agent27P3_old_oracle_false :
    lassoDecisionOracle agent27P3 6 6 12 2 4 = false := by decide
theorem agent27P4_old_oracle_false :
    lassoDecisionOracle agent27P4 6 6 12 2 4 = false := by decide

theorem agent27P0_next :
    firstUnknownPhysical agent27P0 12 finiteBlank = some agent27A0 := by decide
theorem agent27P1_next :
    firstUnknownPhysical agent27P1 12 finiteBlank = some agent27B0 := by decide
theorem agent27P2_next :
    firstUnknownPhysical agent27P2 12 finiteBlank = some agent27C1 := by decide
theorem agent27P3_next :
    firstUnknownPhysical agent27P3 12 finiteBlank = some agent27D1 := by decide
theorem agent27P4_next :
    firstUnknownPhysical agent27P4 12 finiteBlank = some agent27E0 := by decide

private theorem agent27_lasso_open_step
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

/-- Every completion of the four-slot parent reaches the open depth-four
    leaf of the existing physical lasso tree. -/
theorem agent27Parent_open_all (m : Machine)
    (hm : compatible agent27P4 m) :
    agent27Depth4Audit.open m := by
  have hA : m agent27A0 = agent27A0Action :=
    hm agent27A0 agent27A0Action (by decide)
  have hB : m agent27B0 = agent27B0Action :=
    hm agent27B0 agent27B0Action (by decide)
  have hC : m agent27C1 = agent27C1Action :=
    hm agent27C1 agent27C1Action (by decide)
  have hD : m agent27D1 = agent27D1Action :=
    hm agent27D1 agent27D1Action (by decide)
  have h4 :
      (lassoPhysicalTraceAudit agent27P4 6 6 12 12 2 4 0).open m := by
    simp [lassoPhysicalTraceAudit, agent27P4_old_oracle_false]
  have h3 :
      (lassoPhysicalTraceAudit agent27P3 6 6 12 12 2 4 1).open m := by
    apply (agent27_lasso_open_step agent27P3 0 agent27D1
      agent27P3_old_oracle_false agent27P3_next m).2
    simpa [agent27P4, hD] using h4
  have h2 :
      (lassoPhysicalTraceAudit agent27P2 6 6 12 12 2 4 2).open m := by
    apply (agent27_lasso_open_step agent27P2 1 agent27C1
      agent27P2_old_oracle_false agent27P2_next m).2
    simpa [agent27P3, hC] using h3
  have h1 :
      (lassoPhysicalTraceAudit agent27P1 6 6 12 12 2 4 3).open m := by
    apply (agent27_lasso_open_step agent27P1 2 agent27B0
      agent27P1_old_oracle_false agent27P1_next m).2
    simpa [agent27P2, hB] using h2
  have h0 :
      (lassoPhysicalTraceAudit agent27P0 6 6 12 12 2 4 4).open m := by
    apply (agent27_lasso_open_step agent27P0 3 agent27A0
      agent27P0_old_oracle_false agent27P0_next m).2
    simpa [agent27P1, hA] using h1
  simpa [agent27Depth4Audit, agent27P0] using h0

noncomputable def agent27GraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate agent27Depth4Audit agent27WordPump
    (agent27WordPump_cover 6)

/-- Exact open-set semantics of the integrated five-slot graft. -/
theorem agent27GraftedAudit_open_iff (m : Machine) :
    agent27GraftedAudit.open m ↔
      agent27Depth4Audit.open m ∧
        ¬ compatible agent27WordPump m := by
  simpa [agent27GraftedAudit] using
    (addCertificate_open_iff agent27Depth4Audit agent27WordPump
      (agent27WordPump_cover 6) m (empty_compatible m))

/-- On the P4 parent, the grafted open set is exactly the complement of
    Agent 27's five-slot cylinder. -/
theorem agent27P4_exact_open_partition (m : Machine)
    (hm : compatible agent27P4 m) :
    agent27GraftedAudit.open m ↔
      ¬ compatible agent27WordPump m := by
  rw [agent27GraftedAudit_open_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨agent27Parent_open_all m hm, h⟩

/-- Compatibility with the five-slot child implies compatibility with P4. -/
theorem agent27WordPump_parent_compatible (m : Machine)
    (hm : compatible agent27WordPump m) :
    compatible agent27P4 m := by
  have hchild : compatible
      (refine agent27P4 agent27E0 agent27E0Action) m := by
    rw [← agent27WordPump_is_P4_child]
    exact hm
  exact ((compatible_refine_iff agent27P4 m agent27E0 (by decide)
    agent27E0Action).mp hchild).1

/-- The new source cylinder was open in the old frontier and is closed by
    the integrated source certificate. -/
theorem agent27_leaf_closed (m : Machine)
    (hm : compatible agent27WordPump m) :
    agent27Depth4Audit.open m ∧
      ¬ agent27GraftedAudit.open m := by
  have hp := agent27WordPump_parent_compatible m hm
  refine ⟨agent27Parent_open_all m hp, ?_⟩
  intro hopen
  exact (agent27P4_exact_open_partition m hp).mp hopen hm

/-- The graft retains the global audit's exhaustive decided/open contract. -/
theorem agent27GraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ agent27GraftedAudit.open m :=
  agent27GraftedAudit.exhaustive m (empty_compatible m)

/-- The integrated audit still conserves the exact total mass of all raw
    six-state, two-symbol tables. -/
theorem agent27GraftedAudit_conserves :
    agent27GraftedAudit.report.1 + agent27GraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := agent27GraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms agent27P0_old_oracle_false
#print axioms agent27P1_old_oracle_false
#print axioms agent27P2_old_oracle_false
#print axioms agent27P3_old_oracle_false
#print axioms agent27P4_old_oracle_false
#print axioms agent27P0_next
#print axioms agent27P1_next
#print axioms agent27P2_next
#print axioms agent27P3_next
#print axioms agent27P4_next
#print axioms agent27Parent_open_all
#print axioms agent27GraftedAudit_open_iff
#print axioms agent27P4_exact_open_partition
#print axioms agent27WordPump_parent_compatible
#print axioms agent27_leaf_closed
#print axioms agent27GraftedAudit_exhaustive
#print axioms agent27GraftedAudit_conserves

end BB6Coverage

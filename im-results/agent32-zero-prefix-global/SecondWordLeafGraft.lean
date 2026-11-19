import ResidualFrontierManifest
import IncrementalAudit
import TranslatedFiniteOracle

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage

/-!
A second, disjoint finite-word leaf in the existing depth-four physical
frontier.  It shares A/0 and B/0 with Agent 32's twoMarkWordPump, then takes
the distinct C/1 = 0RD branch.  The genuine two-step blank-root entry is at
state C/head 0 with ones at cells 0 and 1 (right-word [0,1]).  The five-step
macro translates those two marks one cell right and returns to C.
-/

def secondWordA0 : Slot := (⟨0, by decide⟩, false)
def secondWordB0 : Slot := (⟨1, by decide⟩, false)
def secondWordC1 : Slot := (⟨2, by decide⟩, true)
def secondWordD1 : Slot := (⟨3, by decide⟩, true)
def secondWordE0 : Slot := (⟨4, by decide⟩, false)
def secondWordF1 : Slot := (⟨5, by decide⟩, true)
def secondWordC0 : Slot := (⟨2, by decide⟩, false)

def secondWordA0Action : Transition := some ⟨true, true, 1⟩
def secondWordB0Action : Transition := some ⟨true, false, 2⟩
def secondWordC1Action : Transition := some ⟨false, true, 3⟩
def secondWordD1Action : Transition := some ⟨true, true, 4⟩
def secondWordE0Action : Transition := some ⟨true, false, 5⟩
def secondWordF1Action : Transition := some ⟨true, false, 2⟩
def secondWordC0Action : Transition := some ⟨false, true, 2⟩

/-- Exact first four physical consultations, ending at E/0. -/
def secondWordP0 : PartialMachine := emptyTable
def secondWordP1 : PartialMachine :=
  refine secondWordP0 secondWordA0 secondWordA0Action
def secondWordP2 : PartialMachine :=
  refine secondWordP1 secondWordB0 secondWordB0Action
def secondWordP3 : PartialMachine :=
  refine secondWordP2 secondWordC1 secondWordC1Action
def secondWordP4 : PartialMachine :=
  refine secondWordP3 secondWordD1 secondWordD1Action

/-- The next three source assignments, in audit-slot order C/0, E/0, F/1,
    complete the finite-word pump.  The physical trace consults E/0 first;
    the generic graft recursion is free to inspect C/0 first. -/
def secondWordP5 : PartialMachine :=
  refine secondWordP4 secondWordE0 secondWordE0Action
def secondWordP6 : PartialMachine :=
  refine secondWordP5 secondWordF1 secondWordF1Action
def secondWordWordPump : PartialMachine :=
  refine secondWordP6 secondWordC0 secondWordC0Action

/-- The old lasso/one-marker oracle rejects every prefix through the
    four-assignment parent. -/
theorem secondWordP0_old_oracle_false :
    lassoDecisionOracle secondWordP0 6 6 12 2 4 = false := by decide
theorem secondWordP1_old_oracle_false :
    lassoDecisionOracle secondWordP1 6 6 12 2 4 = false := by decide
theorem secondWordP2_old_oracle_false :
    lassoDecisionOracle secondWordP2 6 6 12 2 4 = false := by decide
theorem secondWordP3_old_oracle_false :
    lassoDecisionOracle secondWordP3 6 6 12 2 4 = false := by decide
theorem secondWordP4_old_oracle_false :
    lassoDecisionOracle secondWordP4 6 6 12 2 4 = false := by decide

/-- The physical first-unknown scanner follows the exact A/0,B/0,C/1,D/1,E/0
    path. -/
theorem secondWordP0_next :
    firstUnknownPhysical secondWordP0 12 finiteBlank = some secondWordA0 := by decide
theorem secondWordP1_next :
    firstUnknownPhysical secondWordP1 12 finiteBlank = some secondWordB0 := by decide
theorem secondWordP2_next :
    firstUnknownPhysical secondWordP2 12 finiteBlank = some secondWordC1 := by decide
theorem secondWordP3_next :
    firstUnknownPhysical secondWordP3 12 finiteBlank = some secondWordD1 := by decide
theorem secondWordP4_next :
    firstUnknownPhysical secondWordP4 12 finiteBlank = some secondWordE0 := by decide

private theorem secondWord_lasso_open_step
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
theorem secondWordParent_open_all (m : Machine)
    (hm : compatible secondWordWordPump m) :
    depth4ResidualAudit.open m := by
  have hA : m secondWordA0 = secondWordA0Action := by
    apply hm
    simp [secondWordWordPump, secondWordP6, secondWordP5, secondWordP4,
      secondWordP3, secondWordP2, secondWordP1, secondWordP0,
      secondWordA0, secondWordB0, secondWordC1, secondWordD1,
      secondWordE0, secondWordF1, secondWordC0,
      secondWordA0Action, secondWordB0Action, secondWordC1Action,
      secondWordD1Action, secondWordE0Action, secondWordF1Action,
      secondWordC0Action, refine, emptyTable]
  have hB : m secondWordB0 = secondWordB0Action := by
    apply hm
    simp [secondWordWordPump, secondWordP6, secondWordP5, secondWordP4,
      secondWordP3, secondWordP2, secondWordP1, secondWordP0,
      secondWordA0, secondWordB0, secondWordC1, secondWordD1,
      secondWordE0, secondWordF1, secondWordC0,
      secondWordA0Action, secondWordB0Action, secondWordC1Action,
      secondWordD1Action, secondWordE0Action, secondWordF1Action,
      secondWordC0Action, refine, emptyTable]
  have hC : m secondWordC1 = secondWordC1Action := by
    apply hm
    simp [secondWordWordPump, secondWordP6, secondWordP5, secondWordP4,
      secondWordP3, secondWordP2, secondWordP1, secondWordP0,
      secondWordA0, secondWordB0, secondWordC1, secondWordD1,
      secondWordE0, secondWordF1, secondWordC0,
      secondWordA0Action, secondWordB0Action, secondWordC1Action,
      secondWordD1Action, secondWordE0Action, secondWordF1Action,
      secondWordC0Action, refine, emptyTable]
  have hD : m secondWordD1 = secondWordD1Action := by
    apply hm
    simp [secondWordWordPump, secondWordP6, secondWordP5, secondWordP4,
      secondWordP3, secondWordP2, secondWordP1, secondWordP0,
      secondWordA0, secondWordB0, secondWordC1, secondWordD1,
      secondWordE0, secondWordF1, secondWordC0,
      secondWordA0Action, secondWordB0Action, secondWordC1Action,
      secondWordD1Action, secondWordE0Action, secondWordF1Action,
      secondWordC0Action, refine, emptyTable]
  have h4 :
      (lassoPhysicalTraceAudit secondWordP4 6 6 12 12 2 4 0).open m := by
    simp [lassoPhysicalTraceAudit, secondWordP4_old_oracle_false]
  have h3 :
      (lassoPhysicalTraceAudit secondWordP3 6 6 12 12 2 4 1).open m := by
    apply (secondWord_lasso_open_step secondWordP3 0 secondWordD1
      secondWordP3_old_oracle_false secondWordP3_next m).2
    simpa [secondWordP4, hD] using h4
  have h2 :
      (lassoPhysicalTraceAudit secondWordP2 6 6 12 12 2 4 2).open m := by
    apply (secondWord_lasso_open_step secondWordP2 1 secondWordC1
      secondWordP2_old_oracle_false secondWordP2_next m).2
    simpa [secondWordP3, hC] using h3
  have h1 :
      (lassoPhysicalTraceAudit secondWordP1 6 6 12 12 2 4 3).open m := by
    apply (secondWord_lasso_open_step secondWordP1 2 secondWordB0
      secondWordP1_old_oracle_false secondWordP1_next m).2
    simpa [secondWordP2, hB] using h2
  have h0 :
      (lassoPhysicalTraceAudit secondWordP0 6 6 12 12 2 4 4).open m := by
    apply (secondWord_lasso_open_step secondWordP0 3 secondWordA0
      secondWordP0_old_oracle_false secondWordP0_next m).2
    simpa [secondWordP1, hA] using h1
  simpa [depth4ResidualAudit, secondWordP0] using h0

/-- The seven fixed slots define the distinct sibling word pump. -/
theorem secondWordWordPump_is_parent_child :
    secondWordWordPump =
      refine secondWordP6 secondWordC0 secondWordC0Action := rfl

/-- The exact blank-root entry after two moves and the five-step
    translated finite-support macro are accepted by Agent 24's already
    source-verified translated-cycle checker. -/
theorem secondWordWordPump_translated_check :
    finiteTranslatedCheck secondWordWordPump 2 5 = true := by decide

theorem secondWordWordPump_cover (bound : Nat) :
    Cover (DecidedBelow bound) secondWordWordPump :=
  finiteTranslatedCheck_sound secondWordWordPump 2 5 bound
    (by decide) secondWordWordPump_translated_check

/-- Agent 32's two-mark reference cylinder, written explicitly so this
    module does not depend on the still-pending WordOracle import chain. -/
def twoMarkReference : PartialMachine := fun s =>
  if s = (0, false) then some (some ⟨true, true, 1⟩)
  else if s = (1, false) then some (some ⟨true, false, 2⟩)
  else if s = (2, true) then some (some ⟨true, true, 3⟩)
  else if s = (3, true) then some (some ⟨true, true, 4⟩)
  else if s = (4, false) then some (some ⟨true, false, 2⟩)
  else none

/-- The new cylinder diverges from Agent 32's two-mark reference at C/1 and
    is therefore pairwise disjoint from that candidate. -/
theorem secondWord_disjoint_twoMark (m : Machine) :
    ¬ (compatible secondWordWordPump m ∧ compatible twoMarkReference m) := by
  intro h
  have hnew : m secondWordC1 = secondWordC1Action := by
    apply h.1
    simp [secondWordWordPump, secondWordP6, secondWordP5, secondWordP4,
      secondWordP3, secondWordP2, secondWordP1, secondWordP0,
      secondWordA0, secondWordB0, secondWordC1, secondWordD1,
      secondWordE0, secondWordF1, secondWordC0,
      secondWordA0Action, secondWordB0Action, secondWordC1Action,
      secondWordD1Action, secondWordE0Action, secondWordF1Action,
      secondWordC0Action, refine, emptyTable]
  have hold : m secondWordC1 = some ⟨true, true, 3⟩ := by
    apply h.2
    simp [twoMarkReference, secondWordC1]
  have heq : secondWordC1Action = some ⟨true, true, 3⟩ :=
    hnew.symm.trans hold
  simp [secondWordC1Action] at heq

theorem secondWordParent_mass : cylinderMass secondWordP4 = 25^8 := by decide
theorem secondWordChild_mass : cylinderMass secondWordWordPump = 25^5 := by decide

noncomputable def secondWordGraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate depth4ResidualAudit secondWordWordPump
    (secondWordWordPump_cover 6)

/-- Every completion of the new seven-slot cylinder is closed by the
    source-sound word recurrence; all other audit leaves are preserved. -/
theorem secondWordGraftedAudit_closes_source (m : Machine)
    (hm : compatible secondWordWordPump m) :
    ¬ secondWordGraftedAudit.open m := by
  exact addCertificate_closes_source depth4ResidualAudit secondWordWordPump
    (secondWordWordPump_cover 6) m (empty_compatible m) hm

theorem secondWord_leaf_closed (m : Machine)
    (hm : compatible secondWordWordPump m) :
    depth4ResidualAudit.open m ∧ ¬ secondWordGraftedAudit.open m :=
  ⟨secondWordParent_open_all m hm, secondWordGraftedAudit_closes_source m hm⟩

theorem secondWordGraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ secondWordGraftedAudit.open m :=
  secondWordGraftedAudit.exhaustive m (empty_compatible m)

theorem secondWordGraftedAudit_decides_source (m : Machine)
    (hm : compatible secondWordWordPump m) :
    DecidedBelow 6 m := by
  rcases secondWordGraftedAudit_exhaustive m with hgood | hopen
  · exact hgood
  · exact False.elim (secondWordGraftedAudit_closes_source m hm hopen)

theorem secondWordGraftedAudit_conserves :
    secondWordGraftedAudit.report.1 + secondWordGraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := secondWordGraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms secondWordWordPump_translated_check
#print axioms secondWordWordPump_cover
#print axioms secondWord_disjoint_twoMark
#print axioms secondWordParent_open_all
#print axioms secondWordGraftedAudit_closes_source
#print axioms secondWord_leaf_closed
#print axioms secondWordGraftedAudit_exhaustive
#print axioms secondWordGraftedAudit_decides_source
#print axioms secondWordGraftedAudit_conserves

end BB6Coverage

import ResidualFrontierManifest
import IncrementalAudit
import WordOracle

namespace BB6Coverage

/-
Status: source preflight pending. This module is an exact one-leaf graft
candidate, not a new global classifier. It uses the existing depth-four
physical frontier, and the source certificate is Agent 6's finite-word
two-mark glider.
-/

def twoMarkA0 : Slot := (⟨0, by decide⟩, false)
def twoMarkB0 : Slot := (⟨1, by decide⟩, false)
def twoMarkC1 : Slot := (⟨2, by decide⟩, true)
def twoMarkD1 : Slot := (⟨3, by decide⟩, true)
def twoMarkE0 : Slot := (⟨4, by decide⟩, false)

def twoMarkA0Action : Transition := some ⟨true, true, 1⟩
def twoMarkB0Action : Transition := some ⟨true, false, 2⟩
def twoMarkC1Action : Transition := some ⟨true, true, 3⟩
def twoMarkD1Action : Transition := some ⟨true, true, 4⟩
def twoMarkE0Action : Transition := some ⟨true, false, 2⟩

/-- The exact physical prefixes of the two-mark source cylinder. -/
def twoMarkP0 : PartialMachine := emptyTable
def twoMarkP1 : PartialMachine :=
  refine twoMarkP0 twoMarkA0 twoMarkA0Action
def twoMarkP2 : PartialMachine :=
  refine twoMarkP1 twoMarkB0 twoMarkB0Action
def twoMarkP3 : PartialMachine :=
  refine twoMarkP2 twoMarkC1 twoMarkC1Action
def twoMarkP4 : PartialMachine :=
  refine twoMarkP3 twoMarkD1 twoMarkD1Action

theorem twoMarkP0_old_oracle_false :
    lassoDecisionOracle twoMarkP0 6 6 12 2 4 = false := by decide
theorem twoMarkP1_old_oracle_false :
    lassoDecisionOracle twoMarkP1 6 6 12 2 4 = false := by decide
theorem twoMarkP2_old_oracle_false :
    lassoDecisionOracle twoMarkP2 6 6 12 2 4 = false := by decide
theorem twoMarkP3_old_oracle_false :
    lassoDecisionOracle twoMarkP3 6 6 12 2 4 = false := by decide
theorem twoMarkP4_old_oracle_false :
    lassoDecisionOracle twoMarkP4 6 6 12 2 4 = false := by decide

theorem twoMarkP0_next :
    firstUnknownPhysical twoMarkP0 12 finiteBlank = some twoMarkA0 := by decide
theorem twoMarkP1_next :
    firstUnknownPhysical twoMarkP1 12 finiteBlank = some twoMarkB0 := by decide
theorem twoMarkP2_next :
    firstUnknownPhysical twoMarkP2 12 finiteBlank = some twoMarkC1 := by decide
theorem twoMarkP3_next :
    firstUnknownPhysical twoMarkP3 12 finiteBlank = some twoMarkD1 := by decide
theorem twoMarkP4_next :
    firstUnknownPhysical twoMarkP4 12 finiteBlank = some twoMarkE0 := by decide

private theorem lasso_open_step (p : PartialMachine) (d : Nat) (slot : Slot)
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

/-- Every completion of the five-slot word cylinder follows the same
four-edge path through the existing depth-four tree and reaches its open
parent leaf. -/
theorem twoMarkParent_open_all (m : Machine)
    (hm : compatible twoMarkWordPump m) :
    depth4ResidualAudit.open m := by
  have hA : m twoMarkA0 = twoMarkA0Action := by
    apply hm
    simp [twoMarkWordPump, twoMarkA0, twoMarkA0Action]
  have hB : m twoMarkB0 = twoMarkB0Action := by
    apply hm
    simp [twoMarkWordPump, twoMarkB0, twoMarkB0Action]
  have hC : m twoMarkC1 = twoMarkC1Action := by
    apply hm
    simp [twoMarkWordPump, twoMarkC1, twoMarkC1Action]
  have hD : m twoMarkD1 = twoMarkD1Action := by
    apply hm
    simp [twoMarkWordPump, twoMarkD1, twoMarkD1Action]
  have h4 :
      (lassoPhysicalTraceAudit twoMarkP4 6 6 12 12 2 4 0).open m := by
    simp [lassoPhysicalTraceAudit, twoMarkP4_old_oracle_false]
  have h3 :
      (lassoPhysicalTraceAudit twoMarkP3 6 6 12 12 2 4 1).open m := by
    apply (lasso_open_step twoMarkP3 0 twoMarkD1
      twoMarkP3_old_oracle_false twoMarkP3_next m).2
    simpa [twoMarkP4, hD] using h4
  have h2 :
      (lassoPhysicalTraceAudit twoMarkP2 6 6 12 12 2 4 2).open m := by
    apply (lasso_open_step twoMarkP2 1 twoMarkC1
      twoMarkP2_old_oracle_false twoMarkP2_next m).2
    simpa [twoMarkP3, hC] using h3
  have h1 :
      (lassoPhysicalTraceAudit twoMarkP1 6 6 12 12 2 4 3).open m := by
    apply (lasso_open_step twoMarkP1 2 twoMarkB0
      twoMarkP1_old_oracle_false twoMarkP1_next m).2
    simpa [twoMarkP2, hB] using h2
  have h0 :
      (lassoPhysicalTraceAudit twoMarkP0 6 6 12 12 2 4 4).open m := by
    apply (lasso_open_step twoMarkP0 3 twoMarkA0
      twoMarkP0_old_oracle_false twoMarkP0_next m).2
    simpa [twoMarkP1, hA] using h1
  simpa [depth4ResidualAudit, twoMarkP0] using h0

/-- The fifth physical transition is the E/0 child of the open parent. -/
theorem twoMarkWordPump_is_parent_child :
    twoMarkWordPump =
      refine twoMarkP4 twoMarkE0 twoMarkE0Action := by
  funext s
  by_cases hE : s = twoMarkE0
  · subst s
    simp [twoMarkP4, twoMarkP3, twoMarkP2, twoMarkP1, twoMarkP0,
      twoMarkA0, twoMarkB0, twoMarkC1, twoMarkD1, twoMarkE0,
      twoMarkA0Action, twoMarkB0Action, twoMarkC1Action,
      twoMarkD1Action, twoMarkE0Action, twoMarkWordPump, refine, emptyTable]
  · by_cases hD : s = twoMarkD1
    · subst s
      simp [twoMarkP4, twoMarkP3, twoMarkP2, twoMarkP1, twoMarkP0,
        twoMarkA0, twoMarkB0, twoMarkC1, twoMarkD1, twoMarkE0,
        twoMarkA0Action, twoMarkB0Action, twoMarkC1Action,
        twoMarkD1Action, twoMarkE0Action, twoMarkWordPump, refine, emptyTable]
    · by_cases hC : s = twoMarkC1
      · subst s
        simp [twoMarkP4, twoMarkP3, twoMarkP2, twoMarkP1, twoMarkP0,
          twoMarkA0, twoMarkB0, twoMarkC1, twoMarkD1, twoMarkE0,
          twoMarkA0Action, twoMarkB0Action, twoMarkC1Action,
          twoMarkD1Action, twoMarkE0Action, twoMarkWordPump, refine, emptyTable]
      · by_cases hB : s = twoMarkB0
        · subst s
          simp [twoMarkP4, twoMarkP3, twoMarkP2, twoMarkP1, twoMarkP0,
            twoMarkA0, twoMarkB0, twoMarkC1, twoMarkD1, twoMarkE0,
            twoMarkA0Action, twoMarkB0Action, twoMarkC1Action,
            twoMarkD1Action, twoMarkE0Action, twoMarkWordPump, refine, emptyTable]
        · by_cases hA : s = twoMarkA0
          · subst s
            simp [twoMarkP4, twoMarkP3, twoMarkP2, twoMarkP1, twoMarkP0,
              twoMarkA0, twoMarkB0, twoMarkC1, twoMarkD1, twoMarkE0,
              twoMarkA0Action, twoMarkB0Action, twoMarkC1Action,
              twoMarkD1Action, twoMarkE0Action, twoMarkWordPump, refine, emptyTable]
          · simp [twoMarkP4, twoMarkP3, twoMarkP2, twoMarkP1, twoMarkP0,
              twoMarkA0, twoMarkB0, twoMarkC1, twoMarkD1, twoMarkE0,
              twoMarkA0Action, twoMarkB0Action, twoMarkC1Action,
              twoMarkD1Action, twoMarkE0Action, twoMarkWordPump, refine,
              emptyTable, hE, hD, hC, hB, hA]

theorem twoMarkParent_mass : cylinderMass twoMarkP4 = 25^8 := by decide
theorem twoMarkChild_mass : cylinderMass twoMarkWordPump = 25^7 := by decide

noncomputable def twoMarkGraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate depth4ResidualAudit twoMarkWordPump (twoMark_word_cover 6)

/-- All 25^7 completions of the child are closed by the source certificate;
the rest of the original audit remains represented by its certified/open
branches. -/
theorem twoMarkGraftedAudit_closes_source (m : Machine)
    (hm : compatible twoMarkWordPump m) :
    ¬ twoMarkGraftedAudit.open m := by
  exact addCertificate_closes_source depth4ResidualAudit twoMarkWordPump
    (twoMark_word_cover 6) m (empty_compatible m) hm

theorem twoMark_leaf_closed (m : Machine)
    (hm : compatible twoMarkWordPump m) :
    depth4ResidualAudit.open m ∧ ¬ twoMarkGraftedAudit.open m :=
  ⟨twoMarkParent_open_all m hm, twoMarkGraftedAudit_closes_source m hm⟩

theorem twoMarkGraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ twoMarkGraftedAudit.open m :=
  twoMarkGraftedAudit.exhaustive m (empty_compatible m)

theorem twoMarkGraftedAudit_conserves :
    twoMarkGraftedAudit.report.1 + twoMarkGraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := twoMarkGraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms twoMarkParent_open_all
#print axioms twoMarkWordPump_is_parent_child
#print axioms twoMarkGraftedAudit_closes_source
#print axioms twoMark_leaf_closed
#print axioms twoMarkGraftedAudit_exhaustive
#print axioms twoMarkGraftedAudit_conserves

end BB6Coverage

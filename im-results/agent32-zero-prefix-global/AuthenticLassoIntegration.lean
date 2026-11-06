import AuthenticTurnBranchAudit
import FiniteLassoOracle

namespace BB6.F287

open BB6Coverage

/-- The read-one lasso is a source-certified nonhalting cylinder at the same
    bound used by the authentic F287 + turn + two-step global audit. -/
theorem readOneLasso_cover2 :
    Cover (DecidedBelow 2) readOneLassoTable :=
  finiteLassoCheck_sound readOneLassoTable 4 2 readOneLasso_check

/-- The read-one lasso conflicts with the authentic F287 root at B/0. -/
theorem readOneLasso_disjoint_rootCylinder (m : Machine)
    (hL : compatible readOneLassoTable m) (hR : compatible rootCylinder m) : False := by
  let slot : Slot := (⟨1, by decide⟩, false)
  have hL0 := hL slot _ (by simp [readOneLassoTable, slot])
  have hR0 := hR slot _ (by simp [rootCylinder, slot])
  rw [hL0] at hR0
  simp [rootCylinder, original_eq_expectedRLE, expectedRLE, slot] at hR0

/-- The read-one lasso conflicts with the earlier turn cylinder at A/0. -/
theorem readOneLasso_disjoint_turnTable (m : Machine)
    (hL : compatible readOneLassoTable m) (hT : compatible turnTable m) : False := by
  let slot : Slot := (⟨0, by decide⟩, false)
  have hL0 := hL slot _ (by simp [readOneLassoTable, slot])
  have hT0 := hT slot _ (by simp [turnTable, slot])
  rw [hL0] at hT0
  simp [readOneLassoTable, turnTable, slot] at hT0

/-- The read-one lasso conflicts with the earlier two-step halt cylinder at A/0. -/
theorem readOneLasso_disjoint_twoStepHaltTable (m : Machine)
    (hL : compatible readOneLassoTable m)
    (hH : compatible twoStepHaltTable m) : False := by
  let slot : Slot := (⟨0, by decide⟩, false)
  have hL0 := hL slot _ (by simp [readOneLassoTable, slot])
  have hH0 := hH slot _ (by simp [twoStepHaltTable, slot])
  rw [hL0] at hH0
  simp [readOneLassoTable, twoStepHaltTable, turnA, slot] at hH0

/-- The new lasso cylinder is pairwise disjoint from all three cylinders in
    Agent4's authentic F287 + turn + two-step audit. -/
theorem authenticLasso_new_cylinder_disjoint_from_previous (m : Machine)
    (hL : compatible readOneLassoTable m) :
    ¬ compatible rootCylinder m ∧
    ¬ compatible turnTable m ∧
    ¬ compatible twoStepHaltTable m := by
  constructor
  · intro hR
    exact readOneLasso_disjoint_rootCylinder m hL hR
  constructor
  · intro hT
    exact readOneLasso_disjoint_turnTable m hL hT
  · intro hH
    exact readOneLasso_disjoint_twoStepHaltTable m hL hH

/-- Graft the new read-one lasso cylinder into the existing authentic global
    audit, preserving its F287 root and its two earlier certificates. -/
noncomputable def authenticLassoAudit :
    FrontierAudit (DecidedBelow 2) emptyTable :=
  addCertificate authenticTurnBranchAudit readOneLassoTable readOneLasso_cover2

theorem authenticLassoAudit_exhaustive (m : Machine) :
    DecidedBelow 2 m ∨ authenticLassoAudit.open m :=
  authenticLassoAudit.exhaustive m (empty_compatible m)

theorem authenticLassoAudit_conserves :
    authenticLassoAudit.report.1 + authenticLassoAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := authenticLassoAudit.report_conserves
    _ = 25^12 := by decide

/-- Exact sum of the four pairwise-disjoint, source-certified cylinder masses. -/
theorem authenticLasso_known_cylinder_mass :
    cylinderMass rootCylinder + cylinderMass turnTable +
      cylinderMass twoStepHaltTable + cylinderMass readOneLassoTable =
        1 + 2 * 25^9 + 25^10 := by
  calc
    _ = (cylinderMass rootCylinder + cylinderMass turnTable +
        cylinderMass twoStepHaltTable) + cylinderMass readOneLassoTable := by ring
    _ = (1 + 25^9 + 25^10) + 25^9 := by
      rw [authenticTurn_known_cylinder_mass, readOneLasso_mass]
    _ = 1 + 2 * 25^9 + 25^10 := by ring

#print axioms readOneLasso_cover2
#print axioms authenticLasso_new_cylinder_disjoint_from_previous
#print axioms authenticLassoAudit_exhaustive
#print axioms authenticLassoAudit_conserves
#print axioms authenticLasso_known_cylinder_mass

end BB6.F287

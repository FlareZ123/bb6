import CryptidsF287Global
import TurnBranchAudit

namespace BB6.F287

open BB6Coverage

/-- A single global frontier combining one fully source-authenticated
    historical F287 root with the exact-score and turning-sweep cylinders.
    The F287 root remains a certified leaf; every incompatible completion
    stays in the explicit open frontier. -/
noncomputable def authenticTurnBranchAudit :
    FrontierAudit (DecidedBelow 2) emptyTable :=
  addCertificate
    (addCertificate (globalAudit 2) turnTable (turn_example_certificate 2))
    twoStepHaltTable twoStepHaltCertificate

/-- Every canonical six-state table is either decided within score 2 or
    represented by an explicit unresolved leaf of the combined frontier. -/
theorem authenticTurnBranchAudit_exhaustive (m : Machine) :
    DecidedBelow 2 m ∨ authenticTurnBranchAudit.open m :=
  authenticTurnBranchAudit.exhaustive m (empty_compatible m)

/-- The combined frontier preserves the exact 25^12 full-table mass. -/
theorem authenticTurnBranchAudit_mass :
    authenticTurnBranchAudit.report.1 + authenticTurnBranchAudit.report.2 = 25^12 := by
  have h := authenticTurnBranchAudit.report_conserves
  have hf : freeSlotCount emptyTable = 12 := by decide
  simpa [cylinderMass, hf] using h

/-- The historical F287 root is the original Cryptids A6 machine, with an
    independently checked all-time nonhalting proof. -/
theorem authenticF287_root_never : NeverHalts original :=
  original_never

/-- The authentic F287 root cannot overlap either of the two A/0=0RB
    cylinders: its source-verified A/0 action is 1RB. -/
theorem authenticF287_root_disjoint_synthetic (m : Machine)
    (hroot : compatible rootCylinder m)
    (hs : compatible turnTable m ∨ compatible twoStepHaltTable m) : False := by
  have hrootA : m initialSlot = original initialSlot :=
    hroot initialSlot _ (by simp [rootCylinder])
  have hsA : m initialSlot = some turnA := by
    rcases hs with ht | hh
    · exact ht initialSlot _ (by simp [turnTable])
    · exact hh initialSlot _ (by simp [twoStepHaltTable, turnA])
  rw [original_eq_expectedRLE] at hrootA
  have hsource : expectedRLE initialSlot =
      some ⟨true, true, ⟨1, by decide⟩⟩ := by decide
  rw [hsource] at hrootA
  rw [hrootA] at hsA
  simp [turnA] at hsA

/-- The three explicitly described disjoint cylinders contain exactly
    1 + 25^9 + 25^10 complete six-state tables. -/
theorem authenticRoot_cylinder_mass : cylinderMass rootCylinder = 1 := by decide

theorem authenticTurn_known_cylinder_mass :
    cylinderMass rootCylinder + cylinderMass turnTable +
      cylinderMass twoStepHaltTable = 1 + 25^9 + 25^10 := by
  rw [authenticRoot_cylinder_mass, turnTable_cylinder_mass,
      twoStepHaltTable_cylinder_mass]

#print axioms authenticTurnBranchAudit_exhaustive
#print axioms authenticTurnBranchAudit_mass
#print axioms authenticF287_root_never
#print axioms authenticF287_root_disjoint_synthetic

end BB6.F287

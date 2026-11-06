import IncrementalAudit
import FiniteHalting
import RayTurnExample

namespace BB6Coverage

/-- The full-table frontier starts with the real A/0 slot. It certifies
    two disjoint cylinders below the A/0 = 0RB child and leaves every
    alternative branch explicitly unresolved. -/
noncomputable def turnAndHaltAudit : FrontierAudit (DecidedBelow 2) emptyTable :=
  addCertificate
    (graftCertificate emptyTable turnTable (turn_example_certificate 2))
    twoStepHaltTable twoStepHaltCertificate

/-- Every one of the 25^12 canonical six-state tables is represented by
    this audit as either decided within score 2 or in an explicit open leaf. -/
theorem turnAndHaltAudit_exhaustive (m : Machine) :
    DecidedBelow 2 m ∨ turnAndHaltAudit.open m :=
  turnAndHaltAudit.exhaustive m (empty_compatible m)

/-- Every completion of the two-slot A/0=0RB, B/0=halt cylinder halts
    after one ordinary move and the final attempted halt. -/
theorem twoStepHalt_exact_score (m : Machine)
    (hm : compatible twoStepHaltTable m) : HaltsAfter m 1 := by
  let moveA : Move := ⟨false, true, ⟨1, by decide⟩⟩
  have hA : m (⟨0, by decide⟩, false) = some moveA :=
    hm _ _ (by simp [twoStepHaltTable, moveA])
  have hB : m (⟨1, by decide⟩, false) = none :=
    hm _ _ (by simp [twoStepHaltTable])
  have hA' : m (readSlot blank) = some moveA := by
    simpa [readSlot, blank, moveA] using hA
  have hB' : m (readSlot (applyMove blank moveA)) = none := by
    simpa [readSlot, applyMove, blank, moveA] using hB
  have hfirst : run m 1 blank = some (applyMove blank moveA) := by
    simp [run, rawStep, hA']
  have hsecond : run m 2 blank = none := by
    rw [show run m 2 blank = (run m 1 blank).bind (rawStep m) by rfl, hfirst]
    simp [rawStep, hB']
  change (run m 1 blank).isSome = true ∧ run m 2 blank = none
  exact ⟨by rw [hfirst]; rfl, hsecond⟩

/-- The raw Busy Beaver score counts the final halting query, so this
    cylinder has exact score 2. -/
theorem twoStepHalt_score_exact (m : Machine)
    (hm : compatible twoStepHaltTable m) :
    ∃ n, HaltsAfter m n ∧ n + 1 = 2 :=
  ⟨1, twoStepHalt_exact_score m hm, rfl⟩

/-- The three-slot A/0=0RB, B/0=1LC, C/0=1LC cylinder enters a fresh
    leftward blank ray and never halts. -/
theorem turnTable_never (m : Machine)
    (hm : compatible turnTable m) : NeverHalts m := by
  rcases (turn_example_certificate 0).sound m hm with hnever | ⟨n, hbound, _⟩
  · exact hnever
  · omega

/-- These two authentic-root cylinders are both decided by the exact
    source semantics: one has score 2, the other never halts. -/
theorem turnAndHalt_decided_cylinders (m : Machine)
    (h : compatible turnTable m ∨ compatible twoStepHaltTable m) :
    DecidedBelow 2 m := by
  rcases h with ht | hh
  · exact Or.inl (turnTable_never m ht)
  · exact Or.inr ⟨1, by decide, twoStepHalt_exact_score m hh⟩

/-- The cylinders are disjoint because their B/0 actions are distinct. -/
theorem turnAndHalt_cylinders_disjoint :
    ∀ m, ¬ (compatible turnTable m ∧ compatible twoStepHaltTable m) := by
  intro m ⟨ht, hh⟩
  have hturn : m (⟨1, by decide⟩, false) = some turnB :=
    ht _ _ (by simp [turnTable])
  have hhalt : m (⟨1, by decide⟩, false) = none :=
    hh _ _ (by simp [twoStepHaltTable])
  rw [hturn] at hhalt
  cases hhalt

/-- Exact cardinalities of the two disjoint full-table cylinders. -/
theorem turnTable_cylinder_mass : cylinderMass turnTable = 25^9 := by decide

theorem twoStepHaltTable_cylinder_mass :
    cylinderMass twoStepHaltTable = 25^10 := by decide

theorem turnAndHalt_cylinders_mass :
    cylinderMass turnTable + cylinderMass twoStepHaltTable = 25^9 + 25^10 := by
  rw [turnTable_cylinder_mass, twoStepHaltTable_cylinder_mass]

/-- The global audit still accounts for every one of the 25^12 total
    canonical tables; all nonmatching branches remain explicitly open. -/
theorem turnAndHaltAudit_conserves :
    turnAndHaltAudit.report.1 + turnAndHaltAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := turnAndHaltAudit.report_conserves
    _ = 25^12 := by decide

#print axioms turnAndHaltAudit_exhaustive
#print axioms twoStepHalt_exact_score
#print axioms turnTable_never
#print axioms turnAndHalt_cylinders_disjoint
#print axioms turnAndHaltAudit_conserves

end BB6Coverage

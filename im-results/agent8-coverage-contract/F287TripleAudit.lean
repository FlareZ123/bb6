import IncrementalAudit
import F287RootCylinders

namespace BB6.F287
open BB6Coverage

/-- Three source-authenticated rooted 11-fixed-slot nonhalting cylinders
inserted into a single globally exhaustive certified-or-open frontier.
Other six-state machines are deliberately left open. -/
noncomputable def tripleRootAudit (bound : Nat) :
    FrontierAudit (DecidedBelow bound) emptyTable :=
  addCertificate
    (addCertificate
      (addCertificate
        (FrontierAudit.unresolved emptyTable)
        twentyFiveCylinder (twentyFive_cover bound))
      dCylinder (dCylinder_cover bound))
    eCylinder (eCylinder_cover bound)

/-- Any completion of any of the three rooted source cylinders is proved
nonhalting by the imported original A6 certificate and exact root transfers. -/
theorem tripleRootGood (bound : Nat) (full : Machine)
    (h : compatible twentyFiveCylinder full ∨ compatible dCylinder full ∨
      compatible eCylinder full) : DecidedBelow bound full := by
  rcases h with ha | hd | he
  · exact (twentyFive_cover bound).sound full ha
  · exact (dCylinder_cover bound).sound full hd
  · exact (eCylinder_cover bound).sound full he

/-- The resulting 25-way partial frontier is exhaustive even for machines
that belong to no source cylinder; those remain explicitly unresolved. -/
theorem tripleRootExhaustive (bound : Nat) (full : Machine) :
    DecidedBelow bound full ∨ (tripleRootAudit bound).open full :=
  (tripleRootAudit bound).exhaustive full (empty_compatible full)

/-- No machine disappears under the grafts, preserving the exact raw
25^12 table mass, certified plus still-open. -/
theorem tripleRootMass (bound : Nat) :
    (tripleRootAudit bound).report.1 + (tripleRootAudit bound).report.2 =
      25^12 := by
  have h := (tripleRootAudit bound).report_conserves
  have hf : freeSlotCount emptyTable = 12 := by decide
  simpa [cylinderMass, hf] using h

#print axioms tripleRootAudit
#print axioms tripleRootGood
#print axioms tripleRootExhaustive
#print axioms tripleRootMass
end BB6.F287

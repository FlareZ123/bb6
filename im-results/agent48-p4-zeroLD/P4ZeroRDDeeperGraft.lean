import BB6Coverage.P4DeeperFreshRay
import BB6Coverage.EntryMacroOracle

namespace BB6Coverage

/-- The still-open P4 child E/0 = 0RD. -/
def agent48P4ZeroRD : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨false, true, 3⟩)

/-- D/0 = 0RD: one-step rightward fresh ray. -/
def agent48P4ZeroRD_D0ZeroRD : PartialMachine :=
  refine agent48P4ZeroRD agent48D0 (some ⟨false, true, 3⟩)

/-- D/0 = 1RD: one-step rightward fresh ray. -/
def agent48P4ZeroRD_D0OneRD : PartialMachine :=
  refine agent48P4ZeroRD agent48D0 (some ⟨true, true, 3⟩)

/-- D/0 = 1RE: two-step D,E macro returns to D two cells right. -/
def agent48P4ZeroRD_D0OneRE : PartialMachine :=
  refine agent48P4ZeroRD agent48D0 (some ⟨true, true, 4⟩)

/-- D/0 = 0RA: six-step D,A,B,C,D,E macro returns to D four cells right. -/
def agent48P4ZeroRD_D0ZeroRA : PartialMachine :=
  refine agent48P4ZeroRD agent48D0 (some ⟨false, true, 0⟩)

/-- D/0 = 1RA: the same six-step fresh ray with a 1 left behind. -/
def agent48P4ZeroRD_D0OneRA : PartialMachine :=
  refine agent48P4ZeroRD agent48D0 (some ⟨true, true, 0⟩)

/-- D/0 = 1RB: five-step D,B,C,D,E macro returns to D three cells right. -/
def agent48P4ZeroRD_D0OneRB : PartialMachine :=
  refine agent48P4ZeroRD agent48D0 (some ⟨true, true, 1⟩)

theorem agent48P4ZeroRD_D0ZeroRD_check :
    finiteEntryMacroCheck agent48P4ZeroRD_D0ZeroRD 5 1 = true := by decide

theorem agent48P4ZeroRD_D0OneRD_check :
    finiteEntryMacroCheck agent48P4ZeroRD_D0OneRD 5 1 = true := by decide

theorem agent48P4ZeroRD_D0OneRE_check :
    finiteEntryMacroCheck agent48P4ZeroRD_D0OneRE 5 2 = true := by decide

theorem agent48P4ZeroRD_D0ZeroRA_check :
    finiteEntryMacroCheck agent48P4ZeroRD_D0ZeroRA 5 6 = true := by decide

theorem agent48P4ZeroRD_D0OneRA_check :
    finiteEntryMacroCheck agent48P4ZeroRD_D0OneRA 5 6 = true := by decide

theorem agent48P4ZeroRD_D0OneRB_check :
    finiteEntryMacroCheck agent48P4ZeroRD_D0OneRB 5 5 = true := by decide

theorem agent48P4ZeroRD_D0ZeroRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRD_D0ZeroRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroRD_D0ZeroRD 5 1 6 (by decide)
    agent48P4ZeroRD_D0ZeroRD_check

theorem agent48P4ZeroRD_D0OneRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRD_D0OneRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroRD_D0OneRD 5 1 6 (by decide)
    agent48P4ZeroRD_D0OneRD_check

theorem agent48P4ZeroRD_D0OneRE_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRD_D0OneRE :=
  finiteEntryMacroCheck_sound agent48P4ZeroRD_D0OneRE 5 2 6 (by decide)
    agent48P4ZeroRD_D0OneRE_check

theorem agent48P4ZeroRD_D0ZeroRA_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRD_D0ZeroRA :=
  finiteEntryMacroCheck_sound agent48P4ZeroRD_D0ZeroRA 5 6 6 (by decide)
    agent48P4ZeroRD_D0ZeroRA_check

theorem agent48P4ZeroRD_D0OneRA_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRD_D0OneRA :=
  finiteEntryMacroCheck_sound agent48P4ZeroRD_D0OneRA 5 6 6 (by decide)
    agent48P4ZeroRD_D0OneRA_check

theorem agent48P4ZeroRD_D0OneRB_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRD_D0OneRB :=
  finiteEntryMacroCheck_sound agent48P4ZeroRD_D0OneRB 5 5 6 (by decide)
    agent48P4ZeroRD_D0OneRB_check

/-- Add six disjoint D/0 fresh-ray cylinders under E/0 = 0RD. -/
noncomputable def agent48P4ZeroRDDeeperAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate
    (addCertificate
      (addCertificate
        (addCertificate
          (addCertificate
            (addCertificate
              agent48P4DeeperAudit
              agent48P4ZeroRD_D0ZeroRD agent48P4ZeroRD_D0ZeroRD_cover)
            agent48P4ZeroRD_D0OneRD agent48P4ZeroRD_D0OneRD_cover)
          agent48P4ZeroRD_D0OneRE agent48P4ZeroRD_D0OneRE_cover)
        agent48P4ZeroRD_D0ZeroRA agent48P4ZeroRD_D0ZeroRA_cover)
      agent48P4ZeroRD_D0OneRA agent48P4ZeroRD_D0OneRA_cover)
    agent48P4ZeroRD_D0OneRB agent48P4ZeroRD_D0OneRB_cover

#print axioms agent48P4ZeroRD_D0ZeroRD_cover
#print axioms agent48P4ZeroRD_D0OneRD_cover
#print axioms agent48P4ZeroRD_D0OneRE_cover
#print axioms agent48P4ZeroRD_D0ZeroRA_cover
#print axioms agent48P4ZeroRD_D0OneRA_cover
#print axioms agent48P4ZeroRD_D0OneRB_cover

end BB6Coverage

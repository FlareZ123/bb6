import P4EightChildGraft
import EntryMacroOracle
import TranslatedFiniteOracle
import EntryMacroLeft
import FiniteHalting

namespace BB6Coverage

/-- E/0 = 0LC, the still-open fifth-slot child of P4. -/
def agent48P4ZeroLC : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨false, false, 2⟩)

/-- The D/0 slot. -/
def agent48D0 : Slot :=
  (⟨3, by decide⟩, false)

/-- D/0 = 0LD: a one-step translated blank configuration to the left. -/
def agent48P4ZeroLC_D0ZeroLD : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨false, false, 3⟩)

/-- D/0 = 0LA: a seven-step translated blank configuration to the right. -/
def agent48P4ZeroLC_D0ZeroLA : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨false, false, 0⟩)

/-- D/0 = 0RA: a seven-step rightward fresh-ray macro. -/
def agent48P4ZeroLC_D0ZeroRA : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨false, true, 0⟩)

/-- D/0 = 1RA: the same fresh-ray macro, leaving a 1 behind. -/
def agent48P4ZeroLC_D0OneRA : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, true, 0⟩)

/-- D/0 = 1RB: a six-step rightward fresh-ray macro. -/
def agent48P4ZeroLC_D0OneRB : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, true, 1⟩)

/-- D/0 = 0RD: a one-step rightward fresh ray. -/
def agent48P4ZeroLC_D0ZeroRD : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨false, true, 3⟩)

/-- D/0 = 1RD: a one-step rightward fresh ray, writing a 1 behind. -/
def agent48P4ZeroLC_D0OneRD : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, true, 3⟩)

/-- D/0 = 1RE: the three-step D,E,C macro returns to D one cell right. -/
def agent48P4ZeroLC_D0OneRE : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, true, 4⟩)

/-- D/0 = 1LD: a one-step leftward fresh-ray macro. -/
def agent48P4ZeroLC_D0OneLD : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, false, 3⟩)

/-- D/0 = halt: the six-move blank entry ends at the assigned halt slot. -/
def agent48P4ZeroLC_D0Halt : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 none

theorem agent48P4ZeroLC_D0ZeroLD_check :
    finiteTranslatedCheck agent48P4ZeroLC_D0ZeroLD 6 1 = true := by decide

theorem agent48P4ZeroLC_D0ZeroLA_check :
    finiteTranslatedCheck agent48P4ZeroLC_D0ZeroLA 6 7 = true := by decide

theorem agent48P4ZeroLC_D0ZeroRA_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0ZeroRA 6 7 = true := by decide

theorem agent48P4ZeroLC_D0OneRA_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0OneRA 6 7 = true := by decide

theorem agent48P4ZeroLC_D0OneRB_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0OneRB 6 6 = true := by decide

theorem agent48P4ZeroLC_D0ZeroRD_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0ZeroRD 6 1 = true := by decide

theorem agent48P4ZeroLC_D0OneRD_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0OneRD 6 1 = true := by decide

theorem agent48P4ZeroLC_D0OneRE_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0OneRE 6 3 = true := by decide

theorem agent48P4ZeroLC_D0OneLD_check :
    finiteEntryMacroLeftCheck agent48P4ZeroLC_D0OneLD 6 1 = true := by decide

theorem agent48P4ZeroLC_D0Halt_check :
    finiteHaltCheck agent48P4ZeroLC_D0Halt 6 = true := by decide

theorem agent48P4ZeroLC_D0ZeroLD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0ZeroLD :=
  finiteTranslatedCheck_sound agent48P4ZeroLC_D0ZeroLD 6 1 6 (by decide)
    agent48P4ZeroLC_D0ZeroLD_check

theorem agent48P4ZeroLC_D0ZeroLA_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0ZeroLA :=
  finiteTranslatedCheck_sound agent48P4ZeroLC_D0ZeroLA 6 7 6 (by decide)
    agent48P4ZeroLC_D0ZeroLA_check

theorem agent48P4ZeroLC_D0ZeroRA_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0ZeroRA :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0ZeroRA 6 7 6 (by decide)
    agent48P4ZeroLC_D0ZeroRA_check

theorem agent48P4ZeroLC_D0OneRA_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneRA :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0OneRA 6 7 6 (by decide)
    agent48P4ZeroLC_D0OneRA_check

theorem agent48P4ZeroLC_D0OneRB_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneRB :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0OneRB 6 6 6 (by decide)
    agent48P4ZeroLC_D0OneRB_check

theorem agent48P4ZeroLC_D0ZeroRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0ZeroRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0ZeroRD 6 1 6 (by decide)
    agent48P4ZeroLC_D0ZeroRD_check

theorem agent48P4ZeroLC_D0OneRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0OneRD 6 1 6 (by decide)
    agent48P4ZeroLC_D0OneRD_check

theorem agent48P4ZeroLC_D0OneRE_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneRE :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0OneRE 6 3 6 (by decide)
    agent48P4ZeroLC_D0OneRE_check

theorem agent48P4ZeroLC_D0OneLD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneLD :=
  finiteEntryMacroLeftCheck_sound agent48P4ZeroLC_D0OneLD 6 1 6
    (by decide) agent48P4ZeroLC_D0OneLD_check

theorem agent48P4ZeroLC_D0Halt_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0Halt :=
  finiteHaltCheck_sound agent48P4ZeroLC_D0Halt 6 6 (by decide)
    agent48P4ZeroLC_D0Halt_check

/-- The original eight D/0 certificates under E/0 = 0LC. -/
noncomputable def agent48P4DeeperAuditBase :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate
    (addCertificate
      (addCertificate
        (addCertificate
          (addCertificate
            (addCertificate
              (addCertificate
                (addCertificate
                  agent48P4EightChildAudit
                  agent48P4ZeroLC_D0ZeroLD agent48P4ZeroLC_D0ZeroLD_cover)
                agent48P4ZeroLC_D0ZeroLA agent48P4ZeroLC_D0ZeroLA_cover)
              agent48P4ZeroLC_D0ZeroRA agent48P4ZeroLC_D0ZeroRA_cover)
            agent48P4ZeroLC_D0OneRA agent48P4ZeroLC_D0OneRA_cover)
          agent48P4ZeroLC_D0OneRB agent48P4ZeroLC_D0OneRB_cover)
        agent48P4ZeroLC_D0ZeroRD agent48P4ZeroLC_D0ZeroRD_cover)
      agent48P4ZeroLC_D0OneRD agent48P4ZeroLC_D0OneRD_cover)
    agent48P4ZeroLC_D0OneRE agent48P4ZeroLC_D0OneRE_cover

/-- Add the left-ray and halting D/0 cylinders under E/0 = 0LC. -/
noncomputable def agent48P4DeeperAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate
    (addCertificate
      agent48P4DeeperAuditBase
      agent48P4ZeroLC_D0OneLD agent48P4ZeroLC_D0OneLD_cover)
    agent48P4ZeroLC_D0Halt agent48P4ZeroLC_D0Halt_cover

#print axioms agent48P4ZeroLC_D0ZeroLD_cover
#print axioms agent48P4ZeroLC_D0ZeroLA_cover
#print axioms agent48P4ZeroLC_D0ZeroRA_cover
#print axioms agent48P4ZeroLC_D0OneRA_cover
#print axioms agent48P4ZeroLC_D0OneRB_cover
#print axioms agent48P4ZeroLC_D0ZeroRD_cover
#print axioms agent48P4ZeroLC_D0OneRD_cover
#print axioms agent48P4ZeroLC_D0OneRE_cover
#print axioms agent48P4ZeroLC_D0OneLD_cover
#print axioms agent48P4ZeroLC_D0Halt_cover

end BB6Coverage

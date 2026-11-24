import P4ZeroLDCycle
import EntryMacroOracle
import FiniteHalting
import IncrementalAudit

namespace BB6Coverage

/-- The remaining P4 child E/0 = 0RE: a one-step rightward fresh ray. -/
def agent48P4ZeroRE : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨false, true, 4⟩)

/-- E/0 = 1RE: a one-step rightward fresh ray. -/
def agent48P4OneRE : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨true, true, 4⟩)

/-- E/0 = 1RB: the four-step E,B,C,D macro advances two cells. -/
def agent48P4OneRB : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨true, true, 1⟩)

/-- E/0 = 0RA: the five-step E,A,B,C,D macro advances three cells. -/
def agent48P4ZeroRA : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨false, true, 0⟩)

/-- E/0 = 1RA: the same five-step fresh-ray macro with a marked first cell. -/
def agent48P4OneRA : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨true, true, 0⟩)

/-- E/0 = halt: the four-step P4 entry ends at the assigned halt slot. -/
def agent48P4Halt : PartialMachine :=
  refine agent27P4 agent27E0 none

theorem agent48P4ZeroRE_check :
    finiteEntryMacroCheck agent48P4ZeroRE 4 1 = true := by decide

theorem agent48P4OneRE_check :
    finiteEntryMacroCheck agent48P4OneRE 4 1 = true := by decide

theorem agent48P4OneRB_check :
    finiteEntryMacroCheck agent48P4OneRB 4 4 = true := by decide

theorem agent48P4ZeroRA_check :
    finiteEntryMacroCheck agent48P4ZeroRA 4 5 = true := by decide

theorem agent48P4OneRA_check :
    finiteEntryMacroCheck agent48P4OneRA 4 5 = true := by decide

theorem agent48P4Halt_check :
    finiteHaltCheck agent48P4Halt 4 = true := by decide

theorem agent48P4ZeroRE_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRE :=
  finiteEntryMacroCheck_sound agent48P4ZeroRE 4 1 6 (by decide)
    agent48P4ZeroRE_check

theorem agent48P4OneRE_cover :
    Cover (DecidedBelow 6) agent48P4OneRE :=
  finiteEntryMacroCheck_sound agent48P4OneRE 4 1 6 (by decide)
    agent48P4OneRE_check

theorem agent48P4OneRB_cover :
    Cover (DecidedBelow 6) agent48P4OneRB :=
  finiteEntryMacroCheck_sound agent48P4OneRB 4 4 6 (by decide)
    agent48P4OneRB_check

theorem agent48P4ZeroRA_cover :
    Cover (DecidedBelow 6) agent48P4ZeroRA :=
  finiteEntryMacroCheck_sound agent48P4ZeroRA 4 5 6 (by decide)
    agent48P4ZeroRA_check

theorem agent48P4OneRA_cover :
    Cover (DecidedBelow 6) agent48P4OneRA :=
  finiteEntryMacroCheck_sound agent48P4OneRA 4 5 6 (by decide)
    agent48P4OneRA_check

theorem agent48P4Halt_cover :
    Cover (DecidedBelow 6) agent48P4Halt :=
  finiteHaltCheck_sound agent48P4Halt 4 6 (by decide)
    agent48P4Halt_check

/--
The P4 parent is already grafted at E/0 = 1LC by agent27GraftedAudit.
This extends that exact audit with the disjoint E/0 children:
0LD, 0RE, 1RE, 1RB, 0RA, 1RA, and halt.
-/
noncomputable def agent48P4EightChildAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate
    (addCertificate
      (addCertificate
        (addCertificate
          (addCertificate
            (addCertificate
              (addCertificate
                agent27GraftedAudit
                agent48P4ZeroLD agent48P4ZeroLD_cover)
              agent48P4ZeroRE agent48P4ZeroRE_cover)
            agent48P4OneRE agent48P4OneRE_cover)
          agent48P4OneRB agent48P4OneRB_cover)
        agent48P4ZeroRA agent48P4ZeroRA_cover)
      agent48P4OneRA agent48P4OneRA_cover)
    agent48P4Halt agent48P4Halt_cover

#print axioms agent48P4ZeroRE_cover
#print axioms agent48P4OneRE_cover
#print axioms agent48P4OneRB_cover
#print axioms agent48P4ZeroRA_cover
#print axioms agent48P4OneRA_cover
#print axioms agent48P4Halt_cover

end BB6Coverage

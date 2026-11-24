import BB6Coverage.P4EightChildGraft
import BB6Coverage.EntryMacroOracle

namespace BB6Coverage

/-- E/0 = 0LC, the still-open fifth-slot child of P4. -/
def agent48P4ZeroLC : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨false, false, 2⟩)

/-- The D/0 slot. -/
def agent48D0 : Slot :=
  (⟨3, by decide⟩, false)

/-- D/0 = 0RD: a one-step rightward fresh ray from D on blank tape. -/
def agent48P4ZeroLC_D0ZeroRD : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨false, true, 3⟩)

/-- D/0 = 1RD: the same one-step fresh ray, writing a 1 behind the head. -/
def agent48P4ZeroLC_D0OneRD : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, true, 3⟩)

/-- D/0 = 1RE: the three-step D,E,C macro returns to D one cell right. -/
def agent48P4ZeroLC_D0OneRE : PartialMachine :=
  refine agent48P4ZeroLC agent48D0 (some ⟨true, true, 4⟩)

/--
Six blank-root transitions reach D at head 2 with an entirely blank tape:
A/0, B/0, C/1, D/1, E/0=0LC, C/1.
Then D/0=0RD is a one-step fresh ray.
-/
theorem agent48P4ZeroLC_D0ZeroRD_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0ZeroRD 6 1 = true := by
  decide

/-- The D/0=1RD child has a one-step fresh ray. -/
theorem agent48P4ZeroLC_D0OneRD_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0OneRD 6 1 = true := by
  decide

/-- The D/0=1RE child has a three-step D,E,C fresh-ray macro. -/
theorem agent48P4ZeroLC_D0OneRE_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0OneRE 6 3 = true := by
  decide

/-- Every completion of the D/0=0RD child is nonhalting. -/
theorem agent48P4ZeroLC_D0ZeroRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0ZeroRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0ZeroRD 6 1 6 (by decide)
    agent48P4ZeroLC_D0ZeroRD_check

/-- Every completion of the D/0=1RD child is nonhalting. -/
theorem agent48P4ZeroLC_D0OneRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0OneRD 6 1 6 (by decide)
    agent48P4ZeroLC_D0OneRD_check

/-- Every completion of the D/0=1RE child is nonhalting. -/
theorem agent48P4ZeroLC_D0OneRE_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0OneRE :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0OneRE 6 3 6 (by decide)
    agent48P4P4ZeroLC_D0OneRE_check

/-- Add the three disjoint D/0 fresh-ray cylinders to the P4 eight-child audit. -/
noncomputable def agent48P4DeeperAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate
    (addCertificate
      (addCertificate
        agent48P4EightChildAudit
        agent48P4ZeroLC_D0ZeroRD agent48P4ZeroLC_D0ZeroRD_cover)
      agent48P4ZeroLC_D0OneRD agent48P4ZeroLC_D0OneRD_cover)
    agent48P4ZeroLC_D0OneRE agent48P4ZeroLC_D0OneRE_cover

#print axioms agent48P4ZeroLC_D0ZeroRD_cover
#print axioms agent48P4ZeroLC_D0OneRD_cover
#print axioms agent48P4ZeroLC_D0OneRE_cover

end BB6Coverage

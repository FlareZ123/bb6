import BB6Coverage.P4EightChildGraft
import BB6Coverage.EntryMacroOracle

namespace BB6Coverage

/-- E/0 = 0LC, the still-open fifth-slot child of P4. -/
def agent48P4ZeroLC : PartialMachine :=
  refine agent27P4 agent27E0 (some ⟨false, false, 2⟩)

/-- D/0 = 0RD, the sixth-slot fresh-ray child under E/0 = 0LC. -/
def agent48P4ZeroLC_D0ZeroRD : PartialMachine :=
  refine agent48P4ZeroLC (⟨⟨3, by decide⟩, false⟩)
    (some ⟨false, true, 3⟩)

/--
Six blank-root transitions reach D at head 2 with an entirely blank tape:
A/0, B/0, C/1, D/1, E/0=0LC, C/1.
Then D/0=0RD is a one-step fresh ray.
-/
theorem agent48P4ZeroLC_D0ZeroRD_check :
    finiteEntryMacroCheck agent48P4ZeroLC_D0ZeroRD 6 1 = true := by
  decide

/-- Every completion of this six-slot child is nonhalting. -/
theorem agent48P4ZeroLC_D0ZeroRD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLC_D0ZeroRD :=
  finiteEntryMacroCheck_sound agent48P4ZeroLC_D0ZeroRD 6 1 6 (by decide)
    agent48P4ZeroLC_D0ZeroRD_check

/-- Add the deeper D/0 fresh-ray cylinder to the P4 eight-child audit. -/
noncomputable def agent48P4DeeperAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate agent48P4EightChildAudit
    agent48P4ZeroLC_D0ZeroRD agent48P4ZeroLC_D0ZeroRD_cover

#print axioms agent48P4ZeroLC_D0ZeroRD_cover

end BB6Coverage

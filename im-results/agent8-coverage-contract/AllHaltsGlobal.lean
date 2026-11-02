import CylinderFrontier
import AllHaltsFreedom
import FrontierMass

namespace BB6Coverage

/-- All source entries that already carry an ordinary, nonhalt action. -/
def originalLiveSlots (m : Machine) : List Slot :=
  auditSlots.filter (fun s => m s != none)

theorem originalLiveSlots_nodup (m : Machine) :
    (originalLiveSlots m).Nodup := by
  exact auditSlots_nodup.filter _

theorem sparseOriginalLive_eq (m : Machine) :
    sparseOfSeen m (originalLiveSlots m) = freeAllHalts m := by
  funext s
  by_cases hs : m s = none
  · simp [originalLiveSlots, sparseOfSeen, freeAllHalts, hs]
  · have hmem : s ∈ auditSlots := auditSlots_complete s
    simp [originalLiveSlots, sparseOfSeen, freeAllHalts, hs, hmem]

/-- An authenticated proof for one source machine canonically builds a
complete certified-or-open global 25-way frontier: its live instructions
are fixed; every original halt entry is free. All off-source branches
remain explicitly open. -/
noncomputable def originalNonhaltingAudit (bound : Nat) (m : Machine)
    (hnever : NeverHalts m) :
    FrontierAudit (DecidedBelow bound) emptyTable := by
  have h : Cover (DecidedBelow bound) (sparseOfSeen m (originalLiveSlots m)) := by
    rw [sparseOriginalLive_eq]
    exact freeAllHalts_cover bound m hnever
  exact cylinderGlobal (DecidedBelow bound) m (originalLiveSlots m)
    (originalLiveSlots_nodup m) h

theorem originalNonhaltingAudit_exhaustive
    (bound : Nat) (m table : Machine) (hnever : NeverHalts m) :
    DecidedBelow bound table ∨
      (originalNonhaltingAudit bound m hnever).open table :=
  (originalNonhaltingAudit bound m hnever).exhaustive table (empty_compatible table)

theorem originalNonhaltingAudit_mass
    (bound : Nat) (m : Machine) (hnever : NeverHalts m) :
    (originalNonhaltingAudit bound m hnever).report.1 +
      (originalNonhaltingAudit bound m hnever).report.2 = 25^12 := by
  have h := (originalNonhaltingAudit bound m hnever).report_conserves
  have hf : freeSlotCount emptyTable = 12 := by decide
  simpa [cylinderMass, hf] using h

#print axioms originalLiveSlots_nodup
#print axioms sparseOriginalLive_eq
#print axioms originalNonhaltingAudit
#print axioms originalNonhaltingAudit_exhaustive
#print axioms originalNonhaltingAudit_mass
end BB6Coverage

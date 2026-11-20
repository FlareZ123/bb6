import CertificateBatch
import ThreeSlotFamilyLeafOpen

set_option maxRecDepth 16000
set_option maxHeartbeats 0

namespace BB6Coverage
namespace ThreeSlotFamilies

/-- A family member carries both its all-completions nonhalting certificate
    and the proof that its entire source cylinder was open in the old
    depth-four physical audit. -/
structure FamilyLeafCert where
  table : PartialMachine
  cover : Cover (DecidedBelow 6) table
  parentOpen : ∀ m, compatible table m → familyDepth4Audit.open m

def period3FamilyCerts : List FamilyLeafCert :=
  nonAStates.flatMap fun x =>
    directions.flatMap fun right =>
      allStates.map fun y =>
        { table := period3Table x y right
          cover := period3_cover x y right 6
          parentOpen := period3_parent_open_all x y right }

def period4FamilyCerts : List FamilyLeafCert :=
  nonAStates.flatMap fun x =>
    directions.map fun right =>
      { table := period4Table x right
        cover := period4_cover x right 6
        parentOpen := period4_parent_open_all x right }

def entryOneFamilyCerts : List FamilyLeafCert :=
  nonAStates.flatMap fun x =>
    directions.map fun right =>
      { table := entryOneTable x right
        cover := entryOne_cover x right 6
        parentOpen := entryOne_parent_open_all x right }

def familyCerts : List FamilyLeafCert :=
  period3FamilyCerts ++ period4FamilyCerts ++ entryOneFamilyCerts

/-- Erase the parent-open annotation when passing certificates to the
    generic sequential-graft constructor. -/
def toLeafCertificate (c : FamilyLeafCert) :
    LeafCertificate (DecidedBelow 6) :=
  ⟨c.table, c.cover⟩

def familyLeafCertificates : List (LeafCertificate (DecidedBelow 6)) :=
  familyCerts.map toLeafCertificate

theorem familyCerts_length : familyCerts.length = 80 := by
  decide

theorem familyLeafCertificates_length : familyLeafCertificates.length = 80 := by
  simp [familyLeafCertificates, familyCerts_length]

/-- The dependent certificate list retains the 80-way pairwise conflict
    property. This is a kernel-checked finite proof over the explicit
    parameter lists, not a claim inferred from the search log. -/
theorem familyCerts_pairwise_conflict :
    (familyCerts.map FamilyLeafCert.table).Pairwise partialConflict := by
  decide

theorem familyCerts_pairwise_disjoint (c d : FamilyLeafCert)
    (h : partialConflict c.table d.table) :
    ∀ m, ¬ (compatible c.table m ∧ compatible d.table m) :=
  partialConflict_disjoint c.table d.table h

/-- Sequentially graft all 80 translated certificates into the exact
    depth-four physical audit. -/
noncomputable def familyGraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificates familyDepth4Audit familyLeafCertificates

/-- The resulting open set is exactly the old open set minus the union of
    the 80 source cylinders. Source-incompatible machines are preserved. -/
theorem familyGraftedAudit_open_iff (m : Machine) :
    familyGraftedAudit.open m ↔
      familyDepth4Audit.open m ∧
        ∀ c ∈ familyLeafCertificates, ¬ compatible c.1 m :=
  addCertificates_open_iff familyDepth4Audit familyLeafCertificates m
    (empty_compatible m)

/-- Every one of the 80 source cylinders was open before the batch graft
    and is closed afterwards. -/
theorem familyGraftedAudit_closes_candidate (c : FamilyLeafCert)
    (hc : c ∈ familyCerts) (m : Machine)
    (hm : compatible c.table m) :
    familyDepth4Audit.open m ∧ ¬ familyGraftedAudit.open m := by
  refine ⟨c.parentOpen m hm, ?_⟩
  intro hopen
  have hiff := (familyGraftedAudit_open_iff m).mp hopen
  have hc' : toLeafCertificate c ∈ familyLeafCertificates := by
    apply List.mem_map.mpr
    exact ⟨c, hc, rfl⟩
  exact hiff.2 (toLeafCertificate c) hc' hm

theorem familyGraftedAudit_closes_union (m : Machine)
    (h : ∃ c ∈ familyCerts, compatible c.table m) :
    ¬ familyGraftedAudit.open m := by
  rcases h with ⟨c, hc, hm⟩
  exact (familyGraftedAudit_closes_candidate c hc m hm).2

theorem familyGraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ familyGraftedAudit.open m :=
  familyGraftedAudit.exhaustive m (empty_compatible m)

theorem familyGraftedAudit_conserves :
    familyGraftedAudit.report.1 + familyGraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := familyGraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms familyCerts_length
#print axioms familyCerts_pairwise_conflict
#print axioms familyGraftedAudit_open_iff
#print axioms familyGraftedAudit_closes_candidate
#print axioms familyGraftedAudit_closes_union
#print axioms familyGraftedAudit_exhaustive
#print axioms familyGraftedAudit_conserves

end ThreeSlotFamilies
end BB6Coverage

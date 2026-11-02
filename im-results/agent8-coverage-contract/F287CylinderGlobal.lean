import CylinderFrontier
import F287HaltFreedom

namespace BB6.F287

open BB6Coverage

/-- Eleven genuine pinned source input slots. The remaining F/1 input is
unassigned, and therefore represents all 25 possible actions. -/
def fixedSlots : List Slot := auditSlots.filter (fun s => s != haltInput)

theorem fixedSlots_nodup : fixedSlots.Nodup := by
  exact auditSlots_nodup.filter _

theorem sparse_fixed_eq :
    sparseOfSeen expectedRLE fixedSlots = twentyFiveCylinder := by
  funext s
  by_cases hs : s = haltInput
  · simp [sparseOfSeen, fixedSlots, twentyFiveCylinder, freeHaltCylinder, hs]
  · have hmem : s ∈ auditSlots := auditSlots_complete s
    simp [sparseOfSeen, fixedSlots, twentyFiveCylinder, freeHaltCylinder, hs, hmem]

/-- Source-authenticated global 25-way audit that certifies exactly the
nonhalting F287 11-fixed-slot cylinder, leaving every other choice open. -/
noncomputable def globalTwentyFiveAudit (bound : Nat) :
    FrontierAudit (DecidedBelow bound) emptyTable := by
  have h : Cover (DecidedBelow bound)
      (sparseOfSeen expectedRLE fixedSlots) := by
    rw [sparse_fixed_eq]
    exact twentyFive_cover bound
  exact cylinderGlobal (DecidedBelow bound) expectedRLE fixedSlots fixedSlots_nodup h

theorem globalTwentyFiveAudit_exhaustive (bound : Nat) (m : Machine) :
    DecidedBelow bound m ∨ (globalTwentyFiveAudit bound).open m :=
  (globalTwentyFiveAudit bound).exhaustive m (empty_compatible m)

theorem globalTwentyFiveAudit_mass (bound : Nat) :
    (globalTwentyFiveAudit bound).report.1 +
    (globalTwentyFiveAudit bound).report.2 = 25^12 := by
  have h := (globalTwentyFiveAudit bound).report_conserves
  have hf : freeSlotCount emptyTable = 12 := by decide
  simpa [cylinderMass, hf] using h

#print axioms fixedSlots_nodup
#print axioms sparse_fixed_eq
#print axioms globalTwentyFiveAudit
#print axioms globalTwentyFiveAudit_exhaustive
#print axioms globalTwentyFiveAudit_mass

end BB6.F287

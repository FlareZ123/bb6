import CryptidsF287
import SingletonFrontier

namespace BB6.F287

open BB6Coverage BB6.ConjectureBridge

/-- A global BB6 search tree with a single completely pinned, source-authentic
F287/A6 certified leaf. Every off-root transition enters an explicitly open
cylinder, and all 25 possible actions appear at each relevant split slot. -/
noncomputable def globalAudit (bound : Nat) :
    FrontierAudit (DecidedBelow bound) emptyTable := by
  change FrontierAudit (DecidedBelow bound) (fun _ => none)
  exact singletonGlobal (DecidedBelow bound) original
    (Or.inl original_never)

/-- Its coverage theorem refers to every one of the 25^12 total machines,
including those outside the authenticated original F287 root. -/
theorem globalAudit_exhaustive (bound : Nat) (m : Machine) :
    DecidedBelow bound m ∨ (globalAudit bound).open m := by
  exact (globalAudit bound).exhaustive m (empty_compatible m)

/-- No machine is excluded or silently classified: the separate certified and
open tallies add to the entire total-table search space. -/
theorem globalAudit_mass (bound : Nat) :
    (globalAudit bound).report.1 + (globalAudit bound).report.2 =
      25^12 := by
  have h := (globalAudit bound).report_conserves
  have hf : freeSlotCount emptyTable = 12 := by decide
  simpa [cylinderMass, hf] using h

#print axioms globalAudit_exhaustive
#print axioms globalAudit_mass
end BB6.F287

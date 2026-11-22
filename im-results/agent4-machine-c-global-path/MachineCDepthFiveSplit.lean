import MachineCFrontier
import FrontierMass

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- The first free physical slot after the authenticated four-row
    Machine C open cylinder: B/1, the fifth input consulted by the
    original blank run. -/
def machineCDepthFiveSlot : Slot := (⟨1, by decide⟩, true)

/-- Machine C's actual B/1 instruction is 1RD. -/
def machineCDepthFiveMove : Move := ⟨true, true, ⟨3, by decide⟩⟩

def machineCDepthFiveChild (t : Option Move) : PartialMachine :=
  refine (machineCPrefix 4) machineCDepthFiveSlot t

/-- One source-sound 25-way refinement of the authenticated depth-four
    global open cylinder. Each child is tested with the existing
    all-mask finite-ray oracle (through 18 moves), finite-lasso oracle
    (through length 12), and entry-macro oracle. A passing child receives
    a genuine Cover proof; every other child remains explicitly open. -/
def machineCDepthFiveAudit :
    FrontierAudit (DecidedBelow 6) (machineCPrefix 4) :=
  .branch (machineCPrefix 4) machineCDepthFiveSlot (by decide)
    (fun t _ =>
      if h : lassoDecisionOracle (machineCDepthFiveChild t)
          6 18 12 2 4 = true then
        .certified (machineCDepthFiveChild t)
          (lassoDecisionOracle_sound (machineCDepthFiveChild t)
            6 18 12 2 4 h)
      else
        .unresolved (machineCDepthFiveChild t))

/-- The selected split is exactly the next original physical consultation. -/
theorem machineCDepthFiveSlot_is_next_physical :
    firstUnknownPhysical (machineCPrefix 4) 12 finiteBlank =
      some machineCDepthFiveSlot := by
  decide

/-- The original Machine C child is the fifth authentic prefix, not a
    synthetic transition-table completion. -/
theorem machineCDepthFiveChild_is_actual :
    machineCDepthFiveChild (some machineCDepthFiveMove) =
      machineCPrefix 5 := by
  funext slot
  simp [machineCDepthFiveChild, machineCPrefix, machineCVisited,
    machineCDepthFiveSlot, machineCDepthFiveMove, refine, machineC]

/-- The stronger child oracle does not decide the original Machine C
    child; this split therefore retains the actual holdout. -/
theorem machineCDepthFiveRootOracle_false :
    lassoDecisionOracle
      (machineCDepthFiveChild (some machineCDepthFiveMove))
      6 18 12 2 4 = false := by
  decide

/-- Every completion of the depth-four parent is either certified by a
    source-sound child oracle or belongs to a recorded open child. -/
theorem machineCDepthFiveAudit_exhaustive (m : Machine)
    (hm : compatible (machineCPrefix 4) m) :
    DecidedBelow 6 m ∨ machineCDepthFiveAudit.open m :=
  machineCDepthFiveAudit.exhaustive m hm

/-- Exact conservation of the entire 25^8 parent mass across the 25
    children. This is the parent-level accounting, not the separate
    depth-eleven 25-table subcylinder. -/
theorem machineCDepthFiveAudit_mass_conserved :
    machineCDepthFiveAudit.report.1 +
      machineCDepthFiveAudit.report.2 = 25^8 := by
  calc
    _ = cylinderMass (machineCPrefix 4) :=
      FrontierAudit.report_conserves machineCDepthFiveAudit
    _ = 25^8 := by decide

/-- This one-slot split is exhaustive, but the current bounded lasso
    oracle certifies none of its 25 children. The deeper authenticated
    eleven-input continuation supplies the useful 24-leaf refinement. -/
theorem machineCDepthFiveAudit_no_certified_mass :
    machineCDepthFiveAudit.report.1 = 0 := by
  decide

/-- The original Machine C child remains in the open part of this split. -/
noncomputable local instance machineCDepthFiveRootOpenDecidable :
    Decidable (machineCDepthFiveAudit.open machineC) :=
  FrontierAudit.openDecidable machineCDepthFiveAudit machineC

theorem machineCDepthFiveAudit_root_open :
    machineCDepthFiveAudit.open machineC := by
  decide

/-- Diagnostic child counts; each child has mass 25^7. This intentionally
    evaluates the ordinary 25-element list rather than the dependent audit
    recursor, which is kernel-reducible but not compiler-codegen supported. -/
def machineCDepthFiveDiagnosticCounts : Nat × Nat :=
  choices.foldl
    (fun acc t =>
      if lassoDecisionOracle (machineCDepthFiveChild t) 6 18 12 2 4 then
        (acc.1 + 1, acc.2)
      else
        (acc.1, acc.2 + 1))
    (0, 0)

#eval machineCDepthFiveDiagnosticCounts

#print axioms machineCDepthFiveSlot_is_next_physical
#print axioms machineCDepthFiveChild_is_actual
#print axioms machineCDepthFiveRootOracle_false
#print axioms machineCDepthFiveAudit_exhaustive
#print axioms machineCDepthFiveAudit_mass_conserved
#print axioms machineCDepthFiveAudit_no_certified_mass
#print axioms machineCDepthFiveAudit_root_open

end BB6Coverage

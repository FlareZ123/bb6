import MachineCFrontier

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
  decide

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
  decide

/-- A nontrivial set of children receives all-time certificates. -/
theorem machineCDepthFiveAudit_has_certified_mass :
    0 < machineCDepthFiveAudit.report.1 := by
  decide

/-- The original Machine C child remains in the open part of this split. -/
theorem machineCDepthFiveAudit_root_open :
    machineCDepthFiveAudit.open machineC := by
  decide

/-- Diagnostic: counts are in units of the 25^7 mass of one child. -/
#eval (machineCDepthFiveAudit.report.1 / 25^7,
  machineCDepthFiveAudit.report.2 / 25^7)

#print axioms machineCDepthFiveSlot_is_next_physical
#print axioms machineCDepthFiveChild_is_actual
#print axioms machineCDepthFiveRootOracle_false
#print axioms machineCDepthFiveAudit_exhaustive
#print axioms machineCDepthFiveAudit_mass_conserved
#print axioms machineCDepthFiveAudit_has_certified_mass
#print axioms machineCDepthFiveAudit_root_open

end BB6Coverage

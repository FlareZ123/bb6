import Machine623D1Glider
import Machine623RawLeafReduction

namespace BB6Coverage

/-
A parent-level composition of the existing D/1 split and the eleven-row
subcylinder reduction.  The authentic D/1 branch is followed only along its
six remaining actually visited rows; every off-path sibling remains open.
-/

private def machine623C1Slot : Slot := (⟨2, by decide⟩, true)
private def machine623B1Slot : Slot := (⟨1, by decide⟩, true)
private def machine623A1Slot : Slot := (⟨0, by decide⟩, true)
private def machine623E1Slot : Slot := (⟨4, by decide⟩, true)
private def machine623E0Slot : Slot := (⟨4, by decide⟩, false)
private def machine623F1Slot : Slot := (⟨5, by decide⟩, true)

private def machine623D1RootPrefix : PartialMachine :=
  machine623D1Child (machine623 machine623D1Slot)

private def machine623P6 : PartialMachine :=
  refine machine623D1RootPrefix machine623C1Slot
    (machine623 machine623C1Slot)

private def machine623P7 : PartialMachine :=
  refine machine623P6 machine623B1Slot (machine623 machine623B1Slot)

private def machine623P8 : PartialMachine :=
  refine machine623P7 machine623A1Slot (machine623 machine623A1Slot)

private def machine623P9 : PartialMachine :=
  refine machine623P8 machine623E1Slot (machine623 machine623E1Slot)

private def machine623P10 : PartialMachine :=
  refine machine623P9 machine623E0Slot (machine623 machine623E0Slot)

private def machine623P11 : PartialMachine :=
  refine machine623P10 machine623F1Slot (machine623 machine623F1Slot)

/-- The six further authentic reads after D/1 are exactly the remaining
    entries in the eleven-row physical prefix. -/
private theorem machine623P11_eq_prefix11 :
    machine623P11 = machine623Prefix 11 := by
  funext s
  rcases s with ⟨q, b⟩
  fin_cases q <;> cases b <;> decide

/-- Split one sparse row, following its authentic transition into the next
    audit and leaving every other one of the 24 outcomes explicitly open. -/
private def machine623ActualPathBranch
    (p : PartialMachine) (slot : Slot)
    (fresh : p slot = none)
    (next : FrontierAudit (DecidedBelow 6)
      (refine p slot (machine623 slot))) :
    FrontierAudit (DecidedBelow 6) p :=
  .branch p slot fresh (fun t _ =>
    if h : t = machine623 slot then
      h.symm ▸ next
    else
      .unresolved (refine p slot t))

/-- Exhaust the authentic D/1 child through the remaining six physical
    reads.  At the resulting eleven-row cylinder, reuse the exact F/0
    terminal split: 24 total machines and the one original #623 table. -/
private def machine623D1RootTailAudit :
    FrontierAudit (DecidedBelow 6) machine623D1RootPrefix :=
  machine623ActualPathBranch machine623D1RootPrefix machine623C1Slot
    (by decide)
    (machine623ActualPathBranch machine623P6 machine623B1Slot
      (by decide)
      (machine623ActualPathBranch machine623P7 machine623A1Slot
        (by decide)
        (machine623ActualPathBranch machine623P8 machine623E1Slot
          (by decide)
          (machine623ActualPathBranch machine623P9 machine623E0Slot
            (by decide)
            (machine623ActualPathBranch machine623P10 machine623F1Slot
              (by decide)
              (machine623P11_eq_prefix11.symm ▸ machine623FinalSlotAudit)))))

/-- A complete parent-level refinement of the original depth-four #623
    open cylinder.  Six D/1 children are certified by the existing ray and
    lasso witnesses.  In the authentic D/1 child, the six subsequent
    physical reads are split exhaustively, with off-path siblings left open;
    the final F/0 row certifies 24 total completions and leaves #623 open. -/
def machine623ParentAudit :
    FrontierAudit (DecidedBelow 6) (machine623Prefix 4) :=
  .branch (machine623Prefix 4) machine623D1Slot machine623D1_unassigned
    (fun t _ =>
      if h : t = some machine623D1ToBLeft0 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToBLeft0_cover)
      else if h : t = some machine623D1ToCLeft0 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToCLeft0_cover)
      else if h : t = some machine623D1ToDLeft0 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToDLeft0_cover)
      else if h : t = some machine623D1ToDLeft1 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToDLeft1_cover)
      else if h : t = some machine623D1ToDRight0 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToDRight0_cover)
      else if h : t = some machine623D1ToCLeft1 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToCLeft1_cover)
      else if h : t = some machine623D1ToDRight1 then
        .certified (machine623D1Child t)
          (by simpa [h] using machine623D1ToDRight1_cover)
      else if h : t = machine623 machine623D1Slot then
        h.symm ▸ machine623D1RootTailAudit
      else
        .unresolved (machine623D1Child t))

/-- Every total machine in the entire depth-four parent is either covered
    by an all-time nonhalting or score-at-most-six certificate, or remains
    in an explicitly recorded open cylinder. -/
theorem machine623ParentAudit_exhaustive (m : Machine)
    (hm : compatible (machine623Prefix 4) m) :
    DecidedBelow 6 m ∨ machine623ParentAudit.open m :=
  machine623ParentAudit.exhaustive m hm

/-- Exact parent-level accounting.  Six whole D/1 children are certified,
    plus 24 singleton F/0 completions inside the authentic D/1 branch.
    The residual open mass is 17 untouched D/1 siblings plus the
    off-path siblings in the authentic branch and the original #623 singleton. -/
theorem machine623ParentAudit_report :
    machine623ParentAudit.report =
      (7 * 25^7 + 24, 18 * 25^7 - 24) := by
  decide

theorem machine623ParentAudit_report_conserves :
    machine623ParentAudit.report.1 +
      machine623ParentAudit.report.2 = 25^8 := by
  calc
    _ = cylinderMass (machine623Prefix 4) :=
      FrontierAudit.report_conserves machine623ParentAudit
    _ = 25^8 := machine623_first_four_mass

/-- The original #623 table is still in the open part of the parent audit.
    This is deliberately not a halting or nonhalting verdict. -/
theorem machine623ParentAudit_root_remains_open :
    machine623ParentAudit.open machine623 := by
  simp [machine623ParentAudit, machine623ActualPathBranch,
    machine623D1RootTailAudit, FrontierAudit.open,
    machine623D1Slot, machine623C1Slot, machine623B1Slot,
    machine623A1Slot, machine623E1Slot, machine623E0Slot,
    machine623F1Slot, machine623P6, machine623P7, machine623P8,
    machine623P9, machine623P10, machine623P11,
    machine623P11_eq_prefix11, machine623D1RootPrefix,
    machine623D1ToBLeft0, machine623D1ToCLeft0,
    machine623D1ToDLeft0, machine623D1ToDLeft1,
    machine623D1ToDRight0, machine623D1ToCLeft1,
    machine623D1ToDRight1, machine623FinalSlotAudit,
    machine623HaltSlot, machine623]

#print axioms machine623ParentAudit_exhaustive
#print axioms machine623ParentAudit_report
#print axioms machine623ParentAudit_report_conserves
#print axioms machine623ParentAudit_root_remains_open

end BB6Coverage

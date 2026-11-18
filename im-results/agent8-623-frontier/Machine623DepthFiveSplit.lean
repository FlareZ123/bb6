import Machine623DeepFrontier

namespace BB6Coverage

set_option maxRecDepth 15000
set_option maxHeartbeats 0

/-- The fifth distinct physical input on the authentic #623 trace. -/
def machine623D1Slot : Slot := (⟨3, by decide⟩, true)

/-- The first four raw rows leave D/1 unassigned. -/
theorem machine623D1_unassigned :
    machine623Prefix 4 machine623D1Slot = none := by decide

/-- D/1 is not merely a convenient sparse-table coordinate: it is the
    next genuinely consulted input after the first four source rows. -/
theorem machine623D1_first_physical_unknown :
    firstUnknownPhysical (machine623Prefix 4) 96 finiteBlank =
      some machine623D1Slot := by decide

/-- Every total completion of the depth-four cylinder reaches D/1 on its
    actual blank-tape run, after the same six primitive moves. -/
theorem machine623D1_reached_by_every_completion (m : Machine)
    (hm : compatible (machine623Prefix 4) m) :
    ∃ k, k < 96 ∧ ∃ d : FinRayCfg,
      run m k blank = some (embedFinRay d) ∧
      readSlot (embedFinRay d) = machine623D1Slot := by
  obtain ⟨k, hk, d, hrun, hslot, _⟩ :=
    firstUnknownPhysical_is_raw_prefix (machine623Prefix 4) m hm 96
      finiteBlank machine623D1Slot machine623D1_first_physical_unknown
  refine ⟨k, hk, d, ?_, ?_⟩
  · simpa only [embedFinRay_blank] using hrun
  · simpa only [readSlot, embedFinRay] using hslot.symm

/-- A child of the depth-four cylinder obtained by fixing D/1. -/
def machine623D1Child (t : Transition) : PartialMachine :=
  refine (machine623Prefix 4) machine623D1Slot t

/-- Five children enter the exact D/0 fresh-left ray. -/
def machine623D1ToBLeft0 : Move :=
  ⟨false, false, ⟨1, by decide⟩⟩
def machine623D1ToCLeft0 : Move :=
  ⟨false, false, ⟨2, by decide⟩⟩
def machine623D1ToDLeft0 : Move :=
  ⟨false, false, ⟨3, by decide⟩⟩
def machine623D1ToDLeft1 : Move :=
  ⟨true, false, ⟨3, by decide⟩⟩
def machine623D1ToDRight0 : Move :=
  ⟨false, true, ⟨3, by decide⟩⟩

/-- The sixth child closes a genuine two-configuration lasso. -/
def machine623D1ToCLeft1 : Move :=
  ⟨true, false, ⟨2, by decide⟩⟩

theorem machine623D1ToBLeft0_ray_check :
    finiteRayCheck (machine623D1Child (some machine623D1ToBLeft0))
      18 false (rayFiniteMask 8) = true := by decide

theorem machine623D1ToCLeft0_ray_check :
    finiteRayCheck (machine623D1Child (some machine623D1ToCLeft0))
      8 false (rayFiniteMask 8) = true := by decide

theorem machine623D1ToDLeft0_ray_check :
    finiteRayCheck (machine623D1Child (some machine623D1ToDLeft0))
      7 false (rayFiniteMask 8) = true := by decide

theorem machine623D1ToDLeft1_ray_check :
    finiteRayCheck (machine623D1Child (some machine623D1ToDLeft1))
      7 false (rayFiniteMask 8) = true := by decide

theorem machine623D1ToDRight0_ray_check :
    finiteRayCheck (machine623D1Child (some machine623D1ToDRight0))
      10 false (rayFiniteMask 8) = true := by decide

theorem machine623D1ToCLeft1_lasso_check :
    finiteLassoCheck (machine623D1Child (some machine623D1ToCLeft1))
      8 = true := by decide

/-- Each accepted finite ray/lasso witness is an all-time theorem for
    every completion of its corresponding raw-table child. -/
theorem machine623D1ToBLeft0_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToBLeft0)) :=
  finiteRayCheck_sound _ 18 false (rayFiniteMask 8) 6
    machine623D1ToBLeft0_ray_check

theorem machine623D1ToCLeft0_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToCLeft0)) :=
  finiteRayCheck_sound _ 8 false (rayFiniteMask 8) 6
    machine623D1ToCLeft0_ray_check

theorem machine623D1ToDLeft0_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToDLeft0)) :=
  finiteRayCheck_sound _ 7 false (rayFiniteMask 8) 6
    machine623D1ToDLeft0_ray_check

theorem machine623D1ToDLeft1_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToDLeft1)) :=
  finiteRayCheck_sound _ 7 false (rayFiniteMask 8) 6
    machine623D1ToDLeft1_ray_check

theorem machine623D1ToDRight0_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToDRight0)) :=
  finiteRayCheck_sound _ 10 false (rayFiniteMask 8) 6
    machine623D1ToDRight0_ray_check

theorem machine623D1ToCLeft1_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToCLeft1)) :=
  finiteLassoCheck_sound _ 8 6 machine623D1ToCLeft1_lasso_check

/-- A source-sound one-level expansion of the 25^8 depth-four raw-table
    cylinder. Seven children are proved all-time nonhalting; the other
    eighteen are deliberately retained as open cylinders. -/
def machine623D1Audit : FrontierAudit (DecidedBelow 6) (machine623Prefix 4) :=
  .branch (machine623Prefix 4) machine623D1Slot machine623D1_unassigned
    (fun t _ =>
      if h : t = some machine623D1ToBLeft0 then
        .certified (machine623D1Child t)
          (by
            apply finiteRayCheck_sound (machine623D1Child t)
              18 false (rayFiniteMask 8) 6
            simpa [machine623D1Child, h] using machine623D1ToBLeft0_ray_check)
      else if h : t = some machine623D1ToCLeft0 then
        .certified (machine623D1Child t)
          (by
            apply finiteRayCheck_sound (machine623D1Child t)
              8 false (rayFiniteMask 8) 6
            simpa [machine623D1Child, h] using machine623D1ToCLeft0_ray_check)
      else if h : t = some machine623D1ToDLeft0 then
        .certified (machine623D1Child t)
          (by
            apply finiteRayCheck_sound (machine623D1Child t)
              7 false (rayFiniteMask 8) 6
            simpa [machine623D1Child, h] using machine623D1ToDLeft0_ray_check)
      else if h : t = some machine623D1ToDLeft1 then
        .certified (machine623D1Child t)
          (by
            apply finiteRayCheck_sound (machine623D1Child t)
              7 false (rayFiniteMask 8) 6
            simpa [machine623D1Child, h] using machine623D1ToDLeft1_ray_check)
      else if h : t = some machine623D1ToDRight0 then
        .certified (machine623D1Child t)
          (by
            apply finiteRayCheck_sound (machine623D1Child t)
              10 false (rayFiniteMask 8) 6
            simpa [machine623D1Child, h] using machine623D1ToDRight0_ray_check)
      else if h : t = some machine623D1ToCLeft1 then
        .certified (machine623D1Child t)
          (by
            apply finiteLassoCheck_sound (machine623D1Child t) 8 6
            simpa [machine623D1Child, h] using machine623D1ToCLeft1_lasso_check)
      else
        .unresolved (machine623D1Child t))

/-- The split is exhaustive for every total machine in the parent
    cylinder; each machine selects its unique D/1 transition. -/
theorem machine623D1Audit_exhaustive (m : Machine)
    (hm : compatible (machine623Prefix 4) m) :
    DecidedBelow 6 m ∨ machine623D1Audit.open m :=
  machine623D1Audit.exhaustive m hm

/-- Exact raw-table accounting: six certified children and nineteen open
    children, each of mass 25^7. -/
theorem machine623D1Audit_report :
    machine623D1Audit.report = (6 * 25^7, 19 * 25^7) := by decide

theorem machine623D1Audit_report_conserves :
    machine623D1Audit.report.1 + machine623D1Audit.report.2 = 25^8 := by
  rw [machine623D1Audit_report]
  decide

/-- The authentic #623 transition at D/1 is 0LA, so the original root
    remains in one of the eighteen unresolved children. -/
theorem machine623D1Audit_root_remains_open :
    machine623D1Audit.open machine623 := by
  simp [machine623D1Audit, FrontierAudit.open, machine623D1Child,
    machine623D1Slot, machine623D1ToBLeft0, machine623D1ToCLeft0,
    machine623D1ToDLeft0, machine623D1ToDLeft1, machine623D1ToDRight0,
    machine623D1ToCLeft1, machine623]

#print axioms machine623D1_reached_by_every_completion
#print axioms machine623D1ToBLeft0_ray_check
#print axioms machine623D1ToCLeft1_lasso_check
#print axioms machine623D1Audit_exhaustive
#print axioms machine623D1Audit_report
#print axioms machine623D1Audit_report_conserves
#print axioms machine623D1Audit_root_remains_open

end BB6Coverage

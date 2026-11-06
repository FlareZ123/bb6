import PhysicalTraceAudit

namespace BB6Coverage

/-- Complete the genuinely reachable A/1 slot in the concrete two-step
    marked-cell return example with a halt instruction, leaving all nine
    other state-symbol input slots totally unconstrained. -/
def returnReadOneHalter : PartialMachine := fun slot =>
  if slot = (⟨0, by decide⟩, false) then
    some (some ⟨true, true, ⟨1, by decide⟩⟩)
  else if slot = (⟨1, by decide⟩, false) then
    some (some ⟨false, false, ⟨0, by decide⟩⟩)
  else if slot = (⟨0, by decide⟩, true) then
    some none
  else none

/-- The original-source finite sparse simulator reads a one in state A
    after two successful moves, then encounters the assigned halt. -/
theorem returnReadOneHalter_check :
    finiteHaltOracle returnReadOneHalter 3 = true := by decide

theorem returnReadOneHalter_cover :
    Cover (DecidedBelow 3) returnReadOneHalter :=
  finiteHaltOracle_sound returnReadOneHalter 3
    returnReadOneHalter_check

/-- Actual finite tape after A/0=1RB then B/0=0LA: the head is back
    at A over the marked one written at the origin. -/
def returnReadOneC : FinRayCfg :=
  { state := ⟨0, by decide⟩, head := 0, ones := [0] }

theorem returnReadOneTwoSteps :
    finitePartialRun returnReadOneHalter 2 finiteBlank =
      some returnReadOneC := by decide

/-- An exact primitive three-step halting proof for *every* compatible
    total six-state transition table, with the read-one final query. -/
theorem returnReadOneHalter_exact (m : Machine)
    (hm : compatible returnReadOneHalter m) : HaltsAfter m 2 := by
  have hr : run m 2 blank = some (embedFinRay returnReadOneC) := by
    have hrun := finitePartialRun_sound returnReadOneHalter m hm
      finiteBlank returnReadOneC 2 returnReadOneTwoSteps
    simpa only [embedFinRay_blank] using hrun
  have hnone : m (returnReadOneC.state,
      finiteTape returnReadOneC returnReadOneC.head) = none :=
    hm _ _ (by decide)
  constructor
  · simp [hr]
  · simp [run, hr, rawStep, readSlot, embedFinRay, hnone]

theorem returnReadOneHalter_mass :
    cylinderMass returnReadOneHalter = 25^9 := by decide

/-- A certified all-machine read-one-dependent leaf over 25^9 distinct
    full raw tables. This is a known easy halter, serving as an interface
    test of the physical-tape rather than hypothetical read-zero semantics. -/
theorem returnReadOneHalter_works (m : Machine)
    (hm : compatible returnReadOneHalter m) :
    DecidedBelow 3 m :=
  returnReadOneHalter_cover.sound m hm

#print axioms returnReadOneHalter_check
#print axioms returnReadOneHalter_cover
#print axioms returnReadOneHalter_exact
#print axioms returnReadOneHalter_mass
#print axioms returnReadOneHalter_works

end BB6Coverage

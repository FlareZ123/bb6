import MachineCElevenFrontier
import MachineCOneSlotAudit
import FrontierMass

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/--
Continue the already-authenticated Machine C depth-four global open leaf.

At stages 4 through 10, branch at the next *actual physical input* consulted
by Machine C. The authentic Machine C outcome continues the path; every other
transition outcome is retained as an explicitly unresolved sibling. At stage
11, reuse the existing one-slot audit of the sole remaining F/0 input.

This is a finite-entry refinement in the existing `FrontierAudit` contract,
not a second classifier and not a decision of Machine C itself.
-/
def machineCPathRefinementFrom (n : Nat) (hn : n ≤ 11) :
    FrontierAudit (DecidedBelow 6) (machineCPrefix n) :=
  if h : n = 11 then
    by
      subst n
      exact machineCOneSlotAudit 6
  else
    have hlt : n < 11 := by omega
    let slot : Slot := machineCVisited[n]!
    have hs : firstUnknownPhysical (machineCPrefix n) 24 finiteBlank =
        some slot := by
      simpa [slot] using machineC_eleven_first_unknown n hlt
    FrontierAudit.branch (machineCPrefix n) slot
      (firstUnknownPhysical_sound (machineCPrefix n) 24 finiteBlank slot hs)
      (fun t _ => by
        by_cases hactual : t = machineC slot
        · subst t
          have hext : refine (machineCPrefix n) slot (machineC slot) =
              machineCPrefix (n+1) := by
            simpa [slot] using machineC_eleven_prefix_ext n hlt
          rw [hext]
          exact machineCPathRefinementFrom (n+1) (by omega)
        · exact FrontierAudit.unresolved (refine (machineCPrefix n) slot t))
termination_by 11 - n
decreasing_by omega

/-- The continuation starts at the exact depth-four leaf of Agent32's
source-sound global lasso/physical-trace tree. -/
def machineCGlobalLeafRefinement : FrontierAudit (DecidedBelow 6)
    (machineCPrefix 4) :=
  machineCPathRefinementFrom 4 (by decide)

/-- Every completion of the selected depth-four leaf is either certified
by the existing coverage contract or retained in an explicit open cylinder. -/
theorem machineCGlobalLeafRefinement_exhaustive (m : Machine)
    (hm : compatible (machineCPrefix 4) m) :
    DecidedBelow 6 m ∨ machineCGlobalLeafRefinement.open m :=
  machineCGlobalLeafRefinement.exhaustive m hm

/-- The terminal one-slot open set is exactly the original Machine C table:
all other F/0 outcomes are certified as total machines. -/
theorem machineCOneSlotAudit_open_iff_original (m : Machine)
    (hm : compatible (machineCPrefix 11) m) :
    (machineCOneSlotAudit 6).open m ↔ m = machineC := by
  have hopen :
      (machineCOneSlotAudit 6).open m ↔ m machineCHaltSlot = none := by
    simp [machineCOneSlotAudit, FrontierAudit.open]
  rw [hopen]
  constructor
  · intro hhalt
    exact machineC_halt_F0_completion_eq_original m hm hhalt
  · intro hEq
    subst m
    rfl

/-- The genuine Machine C remains open after the depth-four leaf is refined
through all eleven authentic physical consultations and the final F/0 split. -/
theorem machineCGlobalLeafRefinement_open :
    machineCGlobalLeafRefinement.open machineC := by
  unfold machineCGlobalLeafRefinement
  exact machineCPathRefinementFrom_open 4 (by decide)
where
  machineCPathRefinementFrom_open (n : Nat) (hn : n ≤ 11) :
      (machineCPathRefinementFrom n hn).open machineC := by
    by_cases h : n = 11
    · subst n
      exact (machineCOneSlotAudit_open_iff_original machineC
        (machineCPrefix_compatible 11)).2 rfl
    · have hlt : n < 11 := by omega
      let slot : Slot := machineCVisited[n]!
      simp [machineCPathRefinementFrom, h, FrontierAudit.open, slot]
      exact machineCPathRefinementFrom_open (n+1) (by omega)
  termination_by 11 - n
  decreasing_by omega

/-- The continuation is attached to the existing authenticated global path,
rather than a synthetic all-zero control path. -/
theorem machineC_depth_four_leaf_continued :
    (lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4).open machineC ∧
      machineCGlobalLeafRefinement.open machineC :=
  ⟨machineC_depth_four_open, machineCGlobalLeafRefinement_open⟩

/-- Exact raw-table accounting for the selected leaf: 24 of its 25^8
completions are source-certified nonhalting tables; every other completion,
including the original Machine C, remains open. -/
theorem machineCGlobalLeafRefinement_report :
    machineCGlobalLeafRefinement.report = (24, 25^8 - 24) := by
  decide

/-- Generic frontier mass conservation independently checks the total
compatible-table mass of the continuation. -/
theorem machineCGlobalLeafRefinement_mass_conserves :
    machineCGlobalLeafRefinement.report.1 +
      machineCGlobalLeafRefinement.report.2 =
        cylinderMass (machineCPrefix 4) :=
  FrontierAudit.report_conserves machineCGlobalLeafRefinement

#print axioms machineCGlobalLeafRefinement_exhaustive
#print axioms machineCOneSlotAudit_open_iff_original
#print axioms machineCGlobalLeafRefinement_open
#print axioms machineC_depth_four_leaf_continued
#print axioms machineCGlobalLeafRefinement_report
#print axioms machineCGlobalLeafRefinement_mass_conserves

end BB6Coverage

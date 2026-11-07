import MachineCF0Root
import TotalHaltAudit

namespace BB6Coverage

/-- Every Machine C input except its original F/0 halt entry has an
    ordinary, nonhalting transition. -/
theorem machineC_other_rows_live (s : Slot)
    (hs : s ≠ machineCHaltSlot) : machineC s ≠ none := by
  intro h
  exact hs ((machineC_only_halt_row s).mp h)

/-- A completion that changes F/0 from HALT to any of the other 24
    outcomes has no halting transition anywhere. This proof applies to
    the *original authenticated physical-trace prefix*, not a synthetic
    transition table. -/
theorem machineC_ordinary_F0_completion_never
    (t : Transition) (ht : t ≠ none)
    (m : Machine)
    (hm : compatible
      (refine (machineCPrefix 11) machineCHaltSlot t) m) :
    NeverHalts m := by
  apply total_never m
  intro s
  by_cases hs : s = machineCHaltSlot
  · subst s
    have htrow : m machineCHaltSlot = t := hm
      machineCHaltSlot t (by simp [refine])
    simpa only [htrow] using ht
  · have hp := machineCPrefix_eleven_all_other_rows s hs
    have hfixed : refine (machineCPrefix 11) machineCHaltSlot t s =
        some (machineC s) := by
      simpa only [refine, if_neg hs] using hp
    rw [hm s (machineC s) hfixed]
    exact machineC_other_rows_live s hs

/-- The authentic eleven-row Machine C cylinder has 25 completions.
    At F/0, 24 choices have an unconditional nonhalting certificate;
    the sole unresolved child is the original Machine C halt action. -/
def machineCOneSlotAudit (bound : Nat) :
    FrontierAudit (DecidedBelow bound) (machineCPrefix 11) := by
  refine .branch (machineCPrefix 11) machineCHaltSlot (by decide) ?_
  intro t _
  by_cases ht : t = none
  · exact .unresolved
      (refine (machineCPrefix 11) machineCHaltSlot t)
  · apply FrontierAudit.certified
    apply Cover.leaf
    intro m hm
    exact Or.inl (machineC_ordinary_F0_completion_never t ht m hm)

/-- A precise certified/open mass split at the genuine Machine C holdout:
    24 fully specified machines nonhalt trivially; one original machine
    remains undecided. -/
theorem machineCOneSlotAudit_mass (bound : Nat) :
    (machineCOneSlotAudit bound).report = (24, 1) := by rfl

theorem machineCOneSlotAudit_exhaustive (bound : Nat)
    (m : Machine) (hm : compatible (machineCPrefix 11) m) :
    DecidedBelow bound m ∨ (machineCOneSlotAudit bound).open m :=
  (machineCOneSlotAudit bound).exhaustive m hm

#print axioms machineC_other_rows_live
#print axioms machineC_ordinary_F0_completion_never
#print axioms machineCOneSlotAudit_mass
#print axioms machineCOneSlotAudit_exhaustive

end BB6Coverage

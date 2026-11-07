import CryptidsHaltIff
import CSourceBridge
import MachineCPath
import TotalHaltAudit

namespace BB6Coverage

/-- Exact unchanged Cryptids source machine for historical holdout #39. -/
def machineCSource : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.machine

/-- Cellwise equality of all twelve original source transitions to the
    separately written raw table used by the actual six-state frontier. -/
theorem machineC_equals_pinned_cryptids :
    machineC = BB6.ConjectureBridge.toAgent8 machineCSource := by
  funext s
  rcases s with ⟨q, b⟩
  fin_cases q <;> cases b <;> rfl

/-- The genuine physical Machine C blank tape halts at some primitive
    attempted transition iff the source-certified three-counter accelerated
    blank entry eventually halts. There is no simulation cutoff. -/
theorem machineC_raw_halts_iff_counter :
    (∃ n, run machineC n blank = none) ↔
      BB6.CReachBridge.RunHalts := by
  rw [machineC_equals_pinned_cryptids]
  exact
    (BB6.ConjectureBridge.conjecture_halts_iff_agent8_halts
      machineCSource).symm.trans
    ((ConjectureMachines.isHalt_toBB_iff_halts
      machineCSource).symm.trans
    (BB6.CSourceBridge.raw_halts_iff_local.trans
      BB6.CSourceBridge.collatz_iff_runHalts))

/-- The unique original halting input in the canonical six-state
    Machine C transition table. -/
def machineCSourceHaltSlot : Slot := (⟨5, by decide⟩, false)

/-- The original eleven physically witnessed transitions form exactly the
    generic single-free-halting-input cylinder. -/
theorem machineCPrefix_eleven_eq_free_source :
    machineCPrefix 11 =
      freeHaltCylinder machineC machineCSourceHaltSlot := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem machineC_source_unique_halt :
    machineC machineCSourceHaltSlot = none := rfl

theorem machineC_source_other_rows_live :
    ∀ s : Slot, s ≠ machineCSourceHaltSlot → machineC s ≠ none := by
  intro s hs
  rcases s with ⟨q,b⟩
  have hall : ∀ q : Fin 6, ∀ b : Bool,
      (q,b) ≠ machineCSourceHaltSlot →
        machineC (q,b) ≠ none := by decide
  exact hall q b hs

/-- Exact, original-source, full-tape, unbounded halting equation for
    *every one of the 25* Machine C transition-table completions:
    the only possibly halting completion retains F/0=HALT, in which case
    the three-counter source accelerator halts iff the physical machine
    halts. All other completions are syntactically total and nonhalting.
    This does not decide the remaining infinite counter reachability. -/
theorem machineC_cylinder_raw_halts_iff_counter
    (m : Machine) (hm : compatible (machineCPrefix 11) m) :
    (∃ n, run m n blank = none) ↔
      m machineCSourceHaltSlot = none ∧
        BB6.CReachBridge.RunHalts := by
  have hfree : compatible
      (freeHaltCylinder machineC machineCSourceHaltSlot) m := by
    simpa only [← machineCPrefix_eleven_eq_free_source] using hm
  by_cases hhalt : m machineCSourceHaltSlot = none
  · have heq : m = machineC :=
      one_halt_freedom_nontrivial_singleton machineC m
        machineCSourceHaltSlot machineC_source_unique_halt hfree hhalt
    constructor
    · intro hh
      exact ⟨hhalt,
        machineC_raw_halts_iff_counter.mp (by simpa only [heq] using hh)⟩
    · rintro ⟨_, hc⟩
      have hh := machineC_raw_halts_iff_counter.mpr hc
      simpa only [heq] using hh
  · have hnever : NeverHalts m :=
      one_halt_freedom_trivial_part machineC m machineCSourceHaltSlot
        machineC_source_other_rows_live hfree hhalt
    constructor
    · rintro ⟨n, hn⟩
      have hsome := hnever n
      simp [hn] at hsome
    · rintro ⟨hs, _⟩
      exact False.elim (hhalt hs)

/-- A future proof that the published three-counter process never stops
    can be plugged *directly* into the complete raw global audit for the
    genuine 25-table cylinder, without another semantic argument. This is
    deliberately conditional: the required all-time arithmetic assumption
    remains open. -/
theorem machineC_counter_nonhalt_closes_physical_cylinder
    (bound : Nat) (hcounter : ¬ BB6.CReachBridge.RunHalts) :
    Cover (DecidedBelow bound) (machineCPrefix 11) := by
  apply Cover.leaf
  intro m hm
  left
  intro n
  cases hr : run m n blank with
  | some c => rfl
  | none =>
    have hhalt :=
      (machineC_cylinder_raw_halts_iff_counter m hm).mp ⟨n, hr⟩
    exact False.elim (hcounter hhalt.2)

#print axioms machineC_counter_nonhalt_closes_physical_cylinder

#print axioms machineCPrefix_eleven_eq_free_source
#print axioms machineC_source_other_rows_live
#print axioms machineC_cylinder_raw_halts_iff_counter

#print axioms machineC_equals_pinned_cryptids
#print axioms machineC_raw_halts_iff_counter

end BB6Coverage

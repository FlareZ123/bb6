import CryptidsHaltIff
import CSourceBridge
import MachineCPath

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

#print axioms machineC_equals_pinned_cryptids
#print axioms machineC_raw_halts_iff_counter

end BB6Coverage

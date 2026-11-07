import Agent8LogConeSource

/-!
Source exact synthetic two-step terminal-parent witnesses for Cryptids #623.
These disprove unconditional two-step safety for all positive-even-a states
and show why authentic blank-root reachability is the central obstruction.
No example is claimed to be blank reachable.
-/

namespace BB6.Agent8SyntheticParentSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem candidate1 : highLevelNext (.D 2 9) = some (.D 10 10) := by decide +kernel
theorem candidate1halt : highLevelNext (.D 10 10) = none := by decide +kernel
theorem candidate2 : highLevelNext (.D 20 0) = some (.D 16 14) := by decide +kernel
theorem candidate2halt : highLevelNext (.D 16 14) = none := by decide +kernel
theorem candidate3 : highLevelNext (.D 38 1) = some (.D 30 25) := by decide +kernel
theorem candidate3halt : highLevelNext (.D 30 25) = none := by decide +kernel

#print axioms candidate1
#print axioms candidate1halt
#print axioms candidate2
#print axioms candidate2halt
#print axioms candidate3
#print axioms candidate3halt
end BB6.Agent8SyntheticParentSource

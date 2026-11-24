import NearPowerExamples
import NearPowerHugeChecks

namespace BB6.Agent41NearPower
open BB6.Agent41FatalInverse BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Even a target with exponent 10^100 can be excluded without constructing its counters. -/
theorem excludedHuge (i : Nat) : run i≠some (.D (targetX (10^100-1)) (targetY (10^100-1))) := by
  have h := fatalState_rep (10^100-1) (by decide +kernel)
  have he : 10^100-1+1=10^100 := by decide +kernel
  rw [he] at h
  exact check_excludes certHuge _ _ _ h checkedHuge i

#print axioms excludedHuge
end BB6.Agent41NearPower

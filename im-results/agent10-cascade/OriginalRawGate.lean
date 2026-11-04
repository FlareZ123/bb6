import OriginalPhysicalGate
import RootMinIndex

namespace Agent10Raw746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeSweep

/-- Strengthen Agent 7's formally transported exact raw-TM halting iff:
    the remaining blank-root fatal reset indices all exceed 100.
    Every n>=101 with n%6 in {4,5} is only a *candidate*; reachability
    of the authentic root remains open. -/
theorem original_machine_halts_iff_surviving_101 :
    IsHalt target ↔
      ∃ n, 101 ≤ n ∧ (n%6=4 ∨ n%6=5) ∧
        ReachC (2,0) (4*2^n-n-4,0) := by
  rw [Agent7Physical746.original_machine_halts_iff_surviving_52]
  constructor
  · rintro ⟨n,_,hmod,hr⟩
    have hn : 101 ≤ n := by
      by_contra hb
      have hsmall : n ≤ 100 := by omega
      exact CascadeRootMinIndex.no_fatal_through_100 n hsmall hr
    exact ⟨n,hn,hmod,hr⟩
  · rintro ⟨n,hn,hmod,hr⟩
    exact ⟨n,by omega,hmod,hr⟩

#print axioms original_machine_halts_iff_surviving_101
end Agent10Raw746

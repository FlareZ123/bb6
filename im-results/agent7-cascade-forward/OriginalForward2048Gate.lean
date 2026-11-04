import OriginalForwardGate
import Forward2048Final

namespace Agent7OriginalForward746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeSweep

/-- Source-linked original six-state raw-machine exact halting gate, combining
    the pinned original physical semantics with the independently kernel
    certified 167-segment first-reset prefix through fatal index 2048. -/
theorem original_machine_halts_iff_surviving_2049 :
    IsHalt target ↔
      ∃ n, 2049 ≤ n ∧ (n%6=4 ∨ n%6=5) ∧
        ReachC (2,0) (CascadeManyShield.fatal n,0) := by
  rw [original_machine_halts_iff_surviving_1025]
  constructor
  · rintro ⟨n,hn,hres,hr⟩
    have hn' : 2049 ≤ n := by
      by_contra hnot
      have hsmall : n ≤ 2048 := by omega
      exact (CascadeForwardCert.no_fatal_survivors_through_2048 n (by omega) hsmall hres) hr
    exact ⟨n,hn',hres,hr⟩
  · rintro ⟨n,hn,hres,hr⟩
    exact ⟨n,by omega,hres,hr⟩

#print axioms original_machine_halts_iff_surviving_2049
end Agent7OriginalForward746

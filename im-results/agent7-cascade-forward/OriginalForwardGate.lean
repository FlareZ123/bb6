import OriginalRawGate
import ForwardCheck1024

namespace Agent7OriginalForward746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeSweep

/-- Original six-state blank-input machine #746 halts exactly if its true
    accelerated source-C reset orbit reaches a fatal index at least 1025,
    in one of the two surviving residue classes. This iff does not decide
    reachability of any such index and does not prove nonhalting. -/
theorem original_machine_halts_iff_surviving_1025 :
    IsHalt target ↔
      ∃ n, 1025 ≤ n ∧ (n%6=4 ∨ n%6=5) ∧
        ReachC (2,0) (CascadeManyShield.fatal n,0) := by
  rw [Agent10Raw746.original_machine_halts_iff_surviving_257]
  constructor
  · rintro ⟨n,hn,hres,hr⟩
    have hn' : 1025 ≤ n := by
      by_contra hnot
      have hsmall : n ≤ 1024 := by omega
      exact (CascadeForwardCert.no_fatal_survivors_through_1024 n (by omega) hsmall hres) hr
    exact ⟨n,hn',hres,hr⟩
  · rintro ⟨n,hn,hres,hr⟩
    exact ⟨n,by omega,hres,hr⟩

#print axioms original_machine_halts_iff_surviving_1025
end Agent7OriginalForward746

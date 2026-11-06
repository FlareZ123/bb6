import OriginalGate268
import FullThrough299

set_option maxHeartbeats 0
namespace Agent44Raw746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeResetInverse CascadeSweep CascadeManyShield CascadeFastReturn

/-- Strengthen the original, unmodified six-state blank-tape machine's
    halting gate using the source-certified through-299 first-reset exclusions.
    The outer existential remains infinite: no halt/nonhalt decision follows. -/
theorem original_machine_halts_iff_surviving_304 :
    IsHalt target ↔
      ∃ n, 304 ≤ n ∧ (n % 6 = 4 ∨ n % 6 = 5) ∧
        rootReachBool (4*2^n-n-4)=true := by
  rw [Agent10Raw746.original_machine_halts_iff_surviving_268]
  constructor
  · rintro ⟨n,hn,hres,hr⟩
    by_cases hbig : 304≤n
    · exact ⟨n,hbig,hres,hr⟩
    · have hsmall : n≤299 := by omega
      have hp : ReachC (2,0) (fatal n,0) :=
        (rootReachBool_source_iff (fatal n)).mp (by simpa [fatal] using hr)
      exact False.elim ((fatal_unreachable_through_299 n (by omega) hsmall hres) hp)
  · rintro ⟨n,hn,hres,hr⟩
    exact ⟨n,by omega,hres,hr⟩

#print axioms original_machine_halts_iff_surviving_304
end Agent44Raw746

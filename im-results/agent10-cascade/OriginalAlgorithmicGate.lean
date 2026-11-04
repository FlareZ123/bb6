import OriginalRawGate
import ReachDecide

namespace Agent10Raw746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeResetInverse

/-- Exact *original unmodified six-state blank-tape TM* halting criterion
    expressed entirely via a terminating and proved-correct executable
    per-target reset-reachability test. The outer existential still spans
    infinitely many n, so BB(6) and this machine's halting remain unresolved. -/
theorem original_machine_halts_iff_algorithmic_gate :
    IsHalt target ↔
      ∃ n, 257≤n ∧ (n%6=4 ∨ n%6=5) ∧
        rootReachBool (4*2^n-n-4)=true := by
  rw [original_machine_halts_iff_surviving_257]
  constructor
  · rintro ⟨n,hn,hmod,hr⟩
    exact ⟨n,hn,hmod,(rootReachBool_source_iff _).mpr hr⟩
  · rintro ⟨n,hn,hmod,hr⟩
    exact ⟨n,hn,hmod,(rootReachBool_source_iff _).mp hr⟩

#print axioms original_machine_halts_iff_algorithmic_gate
end Agent10Raw746

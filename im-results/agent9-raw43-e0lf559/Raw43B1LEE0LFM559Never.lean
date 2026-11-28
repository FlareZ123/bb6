import Raw43B1LEE0LFM559Final
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Complete the existing Raw43/B1LE/E0LF residual-559 sweep decomposition.

The imported file already proves all three parameterized phase transfers.
This module supplies the genuine blank-start entry, composes those phases
into the exact positive-cost recurrence, and transports it to every total
completion of the one-hole residual.  The missing A1 instruction is never
queried by the orbit.
-/

namespace BB6.Agent17Raw43B1LEE0LFM559

open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent9Raw43B1LEE0LFM559

/-- The physical blank orbit reaches the recurrence section after 170 steps. -/
theorem blank_entry :
    run0 table 170 ⟨0,[],[]⟩ = some (family 0) := by
  decide

/-- The three previously proved phases compose to one quadratic section return. -/
theorem growth (n : Nat) :
    run0 table (448*n+612) (family n) = some (family (n+1)) := by
  have H := join0 (phase_to_p2raw n)
    (join0 (phase_p2_to_p4 n) (phase_final_family n))
  have hc :
      (88*n+132) + ((224*n+276) + (136*n+204)) =
        448*n+612 := by omega
  simpa only [hc] using H

/-- Every total machine completing residual 559 follows the unbounded live orbit. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table family 170 (fun n => 448*n+612) blank_entry
  · intro n
    omega
  · exact growth
  · exact hm

#print axioms blank_entry
#print axioms growth
#print axioms never

end BB6.Agent17Raw43B1LEE0LFM559

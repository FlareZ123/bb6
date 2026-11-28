# Extra37: exact three-phase sweep recurrence

The previously unresolved Raw11 Extra37 leaf is `1RB1LB_1RC0LA_0LA0RD_1RE0RF_1LF1RD_---0LB` (only F0 unspecified). Its symbolic orbit reaches, after 16 primitive steps, a B-state at the left blank with right tape `(10)^2 1`. Write B(n) for this boundary configuration with right tape (10)^(2n+2) 1^(3n+1), and A(a,b) for the A-state on a left blank followed by 0 (10)^a 1^b. All unspecified outer cells are blank.

For every natural n the following reachability chain is now Lean-proven:

* B(n) -> A(2n+2,3n+3)
* A(2n+2,3n+3) -> A(2n+3,3n+3)
* A(2n+3,3n+3) -> B(n+1).

The proof uses a three-step local turn and repeated two-step left/right sweeps. Its two reusable subroutines are (i) consume a suffix triple of 1s, increasing an alternating-pair count and the left unary count by one, and (ii) drain an alternating pair at a separating zero, adding a 1 to each side. All sweep lemmas quantify over arbitrary untouched tails; the iteration is inductive and is not extrapolated from samples. The family grows by seven cells per full cycle, making every return positive-cost.

The theorem `BB6.Agent44Extra37Growth.never` proves NeverHalts for every compatible total machine. `cover Bnd` yields a Cover for arbitrary weighted bound. Source: [Agent44Extra37Growth.lean](../im-results/agent44-raw11-holdouts/Agent44Extra37Growth.lean). Locally compiled using Lean 4.36.0-rc2 with source checker dependencies from core artifact 15271118488. Both theorem axiom reports: [propext, Classical.choice, Quot.sound]. This discharges the sole unresolved leaf in the frozen Extra37 scan (run 45896597080); full parent assembly and exact Raw11 roster consumption remain separate tasks. No decrement of the accepted global roster is yet claimed.

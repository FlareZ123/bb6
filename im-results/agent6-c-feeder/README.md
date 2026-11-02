# Agent 6: finite backward-closed certificates for Machine C

**Status: intermediate formal results; BB(6) remains unresolved.** Machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, accelerated blank entry `(5,0,1)`. The counter transition is copied from published Cryptids; the original machine-to-map bridge is external.

Agents 10 and 11 have proved in Lean that this machine halts exactly if a reachable counter state belongs to the family `(0,2*j,4*j+10)`. The present certificates prove unconditional blank-start nonreachability for **j=0,1,2**.

Files and theorems:

- `NoFirstCFeeder.lean`: copied transition, exact finite-iteration semantics, and `blank_ne_feeder_zero`, excluding `(0,0,10)`.
- `CFeederCertificate.lean`: general-purpose kernel-sound backward-closed finite-set checker. The weighted rank `a+2*k+c` is nondecreasing. A list of states of rank at most B is exhaustively checked for predecessor closure across all source states of rank at most B. Theorem `blank_excluded_by_certificate` excludes any target in such a closed set avoiding the initial state for every finite time. Source states with rank above B cannot transition into the set.
- `NoCFeeder1.lean`: 10-state certificate, B=18; proves `blank_ne_feeder_1`, permanently excluding `(0,2,14)`.
- `NoCFeeder2.lean`: 46-state certificate, B=26; proves `blank_ne_feeder_2`, permanently excluding `(0,4,18)`.

All four files compile with Lean 4.36.0-rc2. Axiom audits report `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx` or `native_decide`. Each `by decide` checks a finite bound in Lean's kernel. Compile the two foundational modules to `.olean` files, then compile the two individual certificates with their location in `LEAN_PATH`. No Mathlib or GitHub CI is required.

The remaining j>=3 feeders are open. Checking finitely many individual j cannot resolve the whole family. A parameterized symbolic reverse invariant, or a finite quotient separating the genuine blank trajectory from all feeders, is the next research objective. This repository work belongs in `im-results/`, not `results/`.

Related repository work: `im-results/agent8-rank-barriers/`, `im-results/agent10-c-funnel/`, `im-results/agent11-c-line/`.

# Agent 44: the source-to-digit drain bridge is now available for the S-window product

`DrainDigitStatsSource.lean` now contains `drainB_digit_transducer`, which proves the exact output identities for every successful `drainB) call with source budget `b ≤ ternaryOnes a`. Combined with Agent 22's `drainB_weighted_exact`, the two identities immediately give the evaluator-call equality (R_{\\rm full}=R_{\\rm dig}=n_1+n_2): both formulas express (2aa+dd) as (2a+d+3b+2r), so `omega` cancels the common terms. The first identity gives (D=L-2n_2).

This removes the per-drain digit/source identification as the main blocker for the product automaton, subject to discharging the source budget on each reachable canonical branch and compiling/axiom-auditing the transitive closure. The S-indexed moving window, full L/R carry rectangles, one-low/three-high shift, and buffered overlap still need to close for every reachable phase. Keep the existing 9,968/9,968 diagnostic as finite evidence only; do not replace it with the q-indexed 262-phase set or start another root replay.

The explicit (R_{\\rm full}=R_{\\rm dig}) corollary is not yet packaged as a named theorem; see the proof sketch sent to Agent 1. The current invocation could not run local Lean because the shell tool failed before command execution, so this is source-level review, not a compile claim.

— Agent 44

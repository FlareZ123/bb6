# Raw54 RB23: source-certified nonhalting by run summaries

Exact table: `1RB0RF_1RC1RA_0RD0RB_1LD0LE_1RB0LE_---0LD`. The F0 slot is unrestricted. [Raw54RBRun23.lean](Raw54RBRun23.lean) proves `BB6.Agent8Raw54.RBRun23.never` for every compatible completion. Original-source Lean 4.36.0-rc2 audit [45737895724](https://github.com/FlareZ123/bb6/actions/runs/45737895724) succeeded; artifact `raw54-rb23-certified`, ID 15080365298. No finite-time assumption is used.

The discovery abstraction was prompted by the following exact B-section rewrites (left excludes the scanned cell; right includes it, nearest first, implicitly zero-padded):
- B(L,01T) -> B(01L,T)
- B(L,10T) -> B(11L,T)
- B(L,001T) -> B(11L,0T)
- B(1^a 0 S,000T) -> B(1S,0^(a+1)11T)
- B(1^a 0 S,111T) -> B(1S,0^(a+1)10T)
- 110 would query F0.

A 316-state macro-level discovery invariant suggested a stronger certificate directly at individual transition level. Encode each count n by n for n<3 and 3+((n-3) mod 2) otherwise. The left stack summary retains its first two unary 1-run counts separated by zeros (count 0 allowed); the right stack summary retains its first three alternating bit runs. Trailing all-zero blank is its own state. A write/push deterministically updates the summary; popping may follow any recorded reverse bit-stack edge. Saturate simultaneously the abstract configurations and the edges they generate, starting from blank. At closure there are 1,274 joint configurations, 21 left summaries, 60 right summaries, and 29+95 stack edges. No configuration reads F0. The Lean certificate supplies all numbered deltas, inverse-edge rows and a balanced joint-state tree to the already source-proved IndexedBiDFA soundness theorem. It kernel-checks each subtree; unlisted transitions cannot be used by any certified reachable state.

This closes all 25 choices of F0 in the physical cylinder, including a halt there. Parent RB closure still requires the exact roster consumer and any other unresolved leaf. The theorem is a local nonhalting result, not a global bound.

# Raw45 A1=1LB/B1=0LA: exact five-hole maximum 473

**Theorem (source kernel checked, 2026-11-28):** For
`1RB1LB_1RC0LA_0RD---_1LD1RB_------_------`, every compatible machine is nonhalting or halts in at most 473 steps, counting the halting query. The bound is attained, hence is exact. This covers all 25^5 = 9,765,625 physical completions, including multiple halt instructions and unused slots.

The first missing query is C1 after 11 moves. The 25-way partition is completely checked: 15 one-sided translated cycles, one width-1 n-gram invariant (C1=1RB), four checked E-target subcovers, four state-swapped F-target subcovers, and the halt at 12. The E-target upper bounds are 372, 387, 375, 473 for 0LE, 0RE, 1LE, 1RE, respectively. The swap preserves the distinguished A start and checks all 12 slots of each transported table. The previous attainment witness is `1RB1LB_1RC0LA_0RD1RE_1LD1RB_0RF0RE_---0RD`, with F0 halt.

## New unbounded run-length invariant

The previously unresolved `1RB1LB_1RC0LA_0RD0RE_1LD1RB_1RF---_0LB1LF` (E1 hole) defeats the tested width <=12 n-gram search and single-parameter affine pump search. It is nevertheless nonhalting for all 25 E1 completions.

At D-return, write the head-inclusive left tape nearest first, the right tape empty. The grammar is two zeros, a nonempty run of ones of arbitrary length, and zero-separated nonempty runs. For every noninitial interior run the length is 6k+5 or 6k+7; the last noninitial run has length 6k+5 or 6k+6. The suffix may be empty. Starting D(0011, empty) is reached in three moves from blank.

The proof encodes each run into alternating packets on a leftward B sweep, then decodes on a rightward D sweep. A carry bit records the parity of the encoded length. An exact 28-step packet consumes six alternating bits and appends six ones. The marker decoders in 14 or 20 steps generate a new base run of length 2 or 4 and add three ones to the previous run. The final base is length 2 or 3. Consequently every interior output run is 6k+5 or 6k+7 and the last is 6k+5 or 6k+6. The arbitrary first run is handled by division modulo 2, then modulo 3; the terminal sweep may either extend it or create a new head run. The Lean proof uses induction on the unbounded suffix grammar, not extrapolation from finite simulations, and constructs arbitrarily long positive-time returns, never consulting E1. See `Raw45Re0Grammar.lean.xz` (decompress to inspect the exact 14,198-byte source).

## Reproduce

In [the certificate dossier](../im-results/agent24-raw45-c1re/), run `bash reproduce-full.sh` with Lean 4.36.0-rc2. It builds the previous C1=1RE proof, exact grammar, 75 new generated modules from the three compressed certificate datasets, then `Raw45C1Full.lean`. The exact dependency closure, all 100 child/parent generated modules, grammar, and final theorem were individually compiled locally. The new shell wrapper has not been run in an actual repository checkout; source and generated hashes are pinned. Kernel axiom profiles: grammar returns/never [propext, Quot.sound]; parent cover/exact_parent_max [propext, Classical.choice, Quot.sound].

This is a five-hole local result, not a global BB(6) solution. It does not decrement the canonical open-root count until the remaining Raw45 obligations are covered.

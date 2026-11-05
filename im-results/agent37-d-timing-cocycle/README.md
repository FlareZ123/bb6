# D Cryptid: experimental first-physical-event timing shift outside the regular grammar

**Agent 37, 2026-11-05. Intermediate computational research, not a proof, blank-root decision, or BB(6) bound.**

## Exact question

Original six-state, two-symbol transition table:
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
Use `I_n(s)` for the physically blank-left F-on-zero configuration, with right tape `1^n s 0^∞`. The **first event** after time zero is either entry into the undefined F/1 transition or an F/0 configuration whose entire physical left tape is blank. Syntactic F/0 with nonblank cells left does not qualify. Require `n>=2`.

**Conjectural arbitrary-suffix first-event cocycle.** For every fixed finite binary suffix `s`, branch residue `r∈{2,3,4}`, and `k>=0`, let `n=3k+r`. Suppose the first event of `I_n(s)` is defined in finite time. Then the first event of `I_(n+3)(s)` should have the same type. If it is a return to `I_b(t)`, the shifted start returns to `I_(b+8)(t)`. If it is a halt, both starts halt. In addition, there should exist an integer `m=m(r,s)>=0`, **independent of k**, such that if `T_k` is the first-event time:

- Return: `T_(k+1)-T_k = 24k+61+24m`, equivalently `T_k=12k²+(49+24m)k+T_0`.
- Halt: `T_(k+1)-T_k = 24k+53+24m`, equivalently `T_k=12k²+(41+24m)k+T_0`.

For a halt, the test reports the count of *executed defined transitions* before encountering F/1; the original source model enters frozen state 6 on the next transition. The constant shift cancels when comparing times.

**These are conjectures.** Finite tests also cannot establish that every input eventually has an event. The first-event claim excludes interior nonblank-left F-state visits.

## Finite raw-table evidence

The standalone [shift_first_event.cpp](shift_first_event.cpp) directly implements the eleven defined machine entries, using an explicit two-way tape and a live count of 1 bits strictly left of the head. It canonicalizes the whole right infinite-blank suffix at each qualifying first return. No regular macro model or original-source theorem is imported by the simulator. It compares each start with its n+3 and n+6 shifts, testing equality of the physical outcome, the predicted +8/+16 unary changes, and the 24-step curvature of the timing increments.

On 2026-11-05 the checked-in C++17 program produced:

- **262,136** exhaustive encoded suffix comparisons: all bitstrings length 0–14 (32,767 encodings per unary seed), unary seeds 5,6,7,8,9,10,15,39. No mismatches or timeouts within 1,000,000 primitive transitions. 1,780 original starts halted as their first event.
- **5,000** pseudorandom suffix comparisons, `mt19937_64` seed `20261105`: suffix length 1–160 (first bit 0, last bit 1), `k=0..35`, `r∈{2,3,4}`. No mismatches or timeouts within the same cap; 39 first-event halts. Observed `m` frequencies: `m=0:4720, m=1:244, m=2:33, m=3:2, m=4:1`.
- An independently coded earlier 90,000-trial finite replay for suffixes up to 24 bits and k=1..20 likewise found no mismatch; the checked-in executable is the primary reproducible evidence.

Encoded suffixes with terminal 0 may physically coincide with shorter suffixes; 262,136 counts input encodings rather than distinct physical tapes. Both sets of tests are finite empirical evidence. They do not certify a universal law.

## Internal prior art and mathematical obstacle

Important prior work already proves comparable claims within restricted languages. Agent 2's [DRegularDurationShift.lean](../agent2-cryptid-continuity/DRegularDurationShift.lean) and [DRegularTimedShift.lean](../agent2-cryptid-continuity/DRegularTimedShift.lean) kernel-prove analogous quadratic time laws for its eleven-case **regular** source-connected grammar, including arbitrary numbers of designated returns. Agent 37's [ReturnShift.lean](../agent37-cryptid-model-bridge/ReturnShift.lean) source-certifies an arbitrary A-token family. Agent 2's [boundary-shift study](../agent2-cryptid-continuity/2026-11-03-b-first-and-boundary-shift.md) already reports qualitative finite comparison evidence and a source-certified failure of an **unguarded all-stack** shift: E boundary length 0 halts while length 4 returns. This report does not claim novelty for regular cases or qualitative shift evidence.

The missing assertion is a complete source-connected **all-arbitrary-suffix first-event** conjugacy encompassing exceptional E packets, halts, the exact physical return predicate and first-return minimality. Agent31's [universal prefixes](../agent31-cryptid-boundary/README.md) reduce `I_(3k+r)(0s)` to B/A/E boundary stacks `m=4k+3`, with exact quadratic costs. A possible proof route is a *guarded four-extra-pair simulation*: consuming each triple-token would add 24 primitive steps to the time difference; final physical returns would contribute another 8 relative steps, unlike halts. This simulation is **unproved**, and a carefully chosen irregular input might invalidate it.

Even a fully established first-event cocycle would be an intermediate structural tool. Every unary n has some **synthetic** halting extension, already source-proved by Agent2 in [ExactFirstHalt.lean](../agent2-cryptid-continuity/ExactFirstHalt.lean). The **genuine blank-reachable suffix language** remains the deciding obstacle. The authentic D-family unary seeds 5,9,15,39 remain unresolved.

## Next discriminating action

Try adversarially structured, long irregular E/A packets for an actual counterexample, especially the source-certified E p=2 marker-mutating branch. If the rule survives, develop an original-source guarded alternating-stack simulation with exact halt/return timing. A useful eventual consequence must constrain an **entire actual blank-root feeder**, not merely produce another synthetic cylinder. Keep this evidence in `im-results/` until that mathematical gap is closed.

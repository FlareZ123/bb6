# D-start strict first B return and falsification of unguarded boundary shift

Agent 2, 2026-11-03. **Intermediate original-source theorem and finite counterexample. Neither decides the blank-start machine or BB(6).**

## Quantified source theorem

Machine: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE--- (A..F indices 0..5, halt 6). Original semantics from checksum-pinned Agent31 Boundary, with exact first-F auxiliary files NoEarlierF and PrefixNoF.

Let I(n,y) be the genuine original F-on-zero configuration with completely blank left tape and right tape consisting of n ones followed by an arbitrary finite binary suffix y. **Theorem BB6.CryptidBFirstReturn.full_B_first_return** in [BFirstReturn.lean](BFirstReturn.lean) states for every natural k and all finite y:

* At primitive step T(k) = 12*k*k + 49*k + 40, the entire machine configuration equals I(8*k+9,y), when the start is I(3*k+2,0::y).
* At every positive primitive time t strictly below T(k), no physical F-on-zero return occurs. Physical means state F, scanned zero, and the **entire** left tape blank.

The new all-k source lemma prefixB_positive_noF from [PrefixNoF.lean](PrefixNoF.lean) rules out any earlier F state in the first-delimiter prefix. The existing source-proved sweepB_firstF and full_B establish the suffix-parametric second part and endpoint. The accompanying b_shift_three theorem proves output unary length +8 when the B input has +3 ones, preserving the suffix.

[Original-source Lean CI 41552165484](https://github.com/FlareZ123/bb6/actions/runs/41552165484) succeeded with final theorem axiom audits **[propext, Quot.sound]**, no sorryAx. This proves the **single-return shift restricted to the B sector**, where n=3k+2 and the next bit is 0. It leaves A/E returns, arbitrary repeated macro steps, and real blank-origin reachability open.

## Exact counterexample to a tempting overgeneralization

For alternating left stacks define B(m,y), A(m,y), E(m,y) as the source machine respectively in states B/A/E scanning zero, right tape y, and left nearest-first lists:

* B: (10)^m 11
* A: 0 (10)^m 11
* E: 00 (10)^m 11

The genuine original F-prefix has stack m=4k+3. It would be attractive to extend the four-extra-pairs conjecture to **all m≥0**. This is **false**.

[BoundaryShiftObstructions.lean](BoundaryShiftObstructions.lean), original-source [Lean CI 41552369769](https://github.com/FlareZ123/bb6/actions/runs/41552369769), certifies that E(0,empty) halts at raw step 11 with no prior physical return, while E(4,empty) physically returns at step 19 with no earlier return. The outcomes differ (halt versus return), so a proof of the useful guarded statement cannot merely assume an all-stack induction. Both source proofs are finite kernel evaluations with no nonstandard axioms. This counterexample is outside the genuine m=4k+3 corridor and does not refute the desired guarded relation.

## Reproducible bounded experiment

[boundary_shift_repro.cpp](boundary_shift_repro.cpp) implements the raw six-state table in C++17, tracks the exact count of nonzero cells strictly left of the head, canonicalizes the entire right suffix of a physical first return, and distinguishes halting, return, and timeout.

Use C++17 optimization and arguments maximum-suffix-length, maximum-m, primitive-step-cap. The arguments 15, 3, 1000000 exhaust the 65,535 finite suffix strings of lengths 0..15 at m=3 versus m=7. All three branches had **no mismatches and no unknowns** (finite evidence only):

| Branch | Return pairs | Both halt | Step-time offset of larger minus smaller |
|---|---:|---:|---|
| B | 65,535 | 0 | +8 on every return |
| A | 65,311 | 224 | Returns +8 (54,430), +32 (9,086), +56 (1,523), +80 (245), +104 (26), +128 (1). Halts +0 (190), +24 (32), +48 (2) |
| E | 64,462 | 1,073 | Returns +8; halts +0 |

A second exhaustive bounded test for m=0..15 and suffix lengths 0..9 found actual failures at A m=0,1 and E m=0,1,2; none at B m≥0, A m≥2 or E m≥3 for these tested inputs. These thresholds remain conjectural; there is **no all-time source theorem** outside B. A's variable +24 time increments strongly indicate repeated interactions with the marked stack, suggesting that a uniform fixed-time coupling is inadequate.

All simulated boundary inputs are synthetic; they are not actual all-blank visits. The P1 and Machine C section normal forms are unlike this alternating-stack D boundary, and no automatic transfer of a four-pair portal has been demonstrated.

## Remaining decisive obligations

A guarded, phase-sensitive first-outcome conjugacy for **A and E** when m=4k+3; a proof that it composes with authentic prefix and return-domain guards for every suffix, including halt and divergence; and then a *blank-reachable right-suffix language* for the genuine seeds n=5,9,15,39. Existing universal halting extensions for each unary n demonstrate why unary-length-only invariants are insufficient. Any transfer to P1 or Machine C requires an independently derived relation for those exact rooted machines.

This report belongs in im-results: it establishes neither a new exact Busy Beaver bound nor any rooted holdout decision.

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


## Further source-certified first-return cylinders (03 November)

### E six-ones, arbitrary k and suffix

[Original-source Lean CI 41553239073](https://github.com/FlareZ123/bb6/actions/runs/41553239073) **succeeded**, compiling [E6FirstReturn.lean](E6FirstReturn.lean) with unmodified original Agent31 Boundary, Agent32 CryptidSix and Agent2 strict prefix. The theorem BB6.CryptidE6FirstReturn.full_E_six_first_return proves that, for every natural k and arbitrary finite binary suffix y, the physical F/0 input

    I_(3k+4)(0 111111 0 y)

has its **first** physical F/0 return at exactly 12*k²+49*k+58 source-machine steps, to

    I_(8k+9)(0 10 10 1110 y).

Here the output code is precisely the source-defined packetSix, the nine-bit list [0,1,0,1,0,1,1,1,0]. The symbolic proof checks every intermediate one of the 16 E-boundary entry transitions and reuses the previously source-verified B sweep's strict no-F property. This strengthens the older endpoint-only E6 return; it is a narrow cylinder, not a general E shift.

### Two-parameter first A return with arbitrary number of 10 tokens

[Original-source Lean CI 41554299319](https://github.com/FlareZ123/bb6/actions/runs/41554299319) **succeeded** against the entire original source chain, compiling [ATenFirstReturn.lean](ATenFirstReturn.lean) and the new prefixA_positive_noF in [PrefixNoF.lean](PrefixNoF.lean). The theorem BB6.CryptidATenFirstReturn.full_A_ten_first_return proves, for **all** natural k,q and arbitrary finite right suffix y,

    I_(3k+3)(0 (10)^q 0 y)
       --[12*k²+49*k+44+4*q]--> I_(8k+11+2*q)(y)

as its **strict first positive-time physical F/0 return**. It gives +3 input ones to +8 output ones at the same q and y. This extends Agent35's previously source-checked general A-code endpoint with first-return minimality for the infinite two-parameter 10-only subfamily.

The proof is entirely in the authentic original D-start transition model. It proves universal two-step A token rewriting, induction over q; an independent C-on-one cursor descent through every pair, with four-step close; and strict absence of F throughout both subruns. The original source prefix-A no-F lemma excludes any earlier F during the unary first-delimiter phase. No synthetic equality is substituted for a genuine blank-origin reachability claim.

**Scientific significance and residual:** The A token family now comes with an authenticated first-return relation, but an arbitrary mixed code word in 10/111, E exceptions, and arbitrary right suffix are still open as universal first-outcome shifts. No blank-start holdout status or Busy Beaver bound follows from these local theorems.


### Universal mixed-token A first-return theorem

**Original raw-source Lean CI [41555037075](https://github.com/FlareZ123/bb6/actions/runs/41555037075) succeeded** with [ACodeFirstReturn.lean](ACodeFirstReturn.lean), compiling the checksum-pinned original Agent31 source, Agent25's alternate-halting-state A interpreter, Agent35's exact interpreter-to-original simulation, and our strict prefix-A/closing-cursor lemmas. The code file has no unproved placeholders and prints the axiom dependencies of its main theorem.

Let w be an **arbitrary finite Boolean word**. Define Code(w) by replacing each false token with 10 and each true token with 111. Let inc(w) be the sum of 1 per false and 4 per true. Define cost(m,w) by consuming a 10 token in 2 steps and a 111 token in 6m+41 steps, updating m by +1 or +4 respectively before the next token. Put m=4k+3. The new theorem BB6.CryptidACodeFirstReturn.full_A_mixed_code_first_return proves for **all natural k, all finite w, all finite binary suffixes y**:

    I_(3k+3)(0 Code(w) 0 y)
      --[T]--> I_(2*(m+inc(w))+5)(y)

where T = 12*k*k+41*k+32 + cost(m,w) + (2*(m+inc(w))+6). This endpoint is the **first positive-time physical F-on-zero return**. In particular, adding three unary 1s to the input increases the output unary length by eight, for the same token code and suffix. The time difference is generally code-dependent.

Key proof structure:
1. Prove **no F state anywhere** during the complete 6m+41-step triple (111) token, all m and suffixes. Induct over the intermediate B leftward 4m walk and A rightward 2(m+4) walk, filling every finite 8,8,10,7-step transition segment; all transitions are those of Agent25's alternate source model.
2. Induct over **arbitrary interleavings** of the 10 and 111 tokens to obtain a no-F theorem for their complete decoding time. Transfer it through Agent35's universal source conjugacy to original raw machine, without assuming that the target halted state is injective.
3. Compose with original-source A zero-close first return and original-source prefix-A noF; all three subruns are source-authenticated, and the final endpoint has completely blank left tape.

This strictly strengthens the previous two-parameter (10)^q first-return certificate, whose arbitrary q is recovered by taking w to be q false tokens. It is not an all-suffix theorem: **110** begins an additional exceptional A branch outside Code(w)0. No assertion about the actual blank-origin right suffix entering the code grammar is made. Further source work should tackle the A 1100 exception and E suffix grammar instead of recertifying more individual code words.

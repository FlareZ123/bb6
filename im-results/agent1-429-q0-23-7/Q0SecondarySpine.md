# #429 q0: an unbounded secondary F spine after exactly three FSFE blocks

**Status:** all-depth arithmetic result kernel-checked with Lean 4.36.0-rc2; copied inverse grammar and necessary residue predicates, not original-source import acceptance or a blank-root decision. The result is a limitation on uniform fixed-depth inverse pruning, even after separately accelerating the FSFE spine.

## The theorem

Let

    n = 23+32u
    a0 = 13*2^n - 24u - 19
    b0 = 2a0-13
    w0 = b0-a0-8 = a0-21.

For every natural K there exists a natural u for which the inverse-candidate tree contains the word

    (FSFE)^3 F^K

with all its vertices passing **every** necessary residue test in Agent 6's [depth-16 sieve](../agent6-harmonic429/Q0Depth16InverseSieve.md). The proof checks all branch guards and lower bounds. It does not show that any of the vertices is genuinely reachable from blank.

The all-depth obstruction persists even if the single repeated-FSFE branch is compressed into a single valuation macro: a secondary all-F branch at the *fixed* block index 3 is unbounded.

## Exact three-block transfer

Write w0=4096 w. From a0=w0+21 and b0=2w0+29, the three completed FSFE blocks give

| Block index j | a_j | b_j | w_j |
| --- | --- | --- | --- |
| 0 | 4096w+21 | 8192w+29 | 4096w |
| 1 | 5376w+13 | 5632w+21 | 256w |
| 2 | 5456w+5 | 5472w+13 | 16w |
| 3 | 5461w-3 | 5462w+5 | w |

For w a positive multiple of 64, the twelve edges and all thirteen vertex predicates are valid, with no small-counter exceptions. The rank at index 3 is

    R3 = 2a3+b3 = 16384w-1.

The special cancellation a3+3=5461w makes this a new valuation clock at a fixed prefix, independent of how many further FSFE blocks could have been taken.

For an all-F run from this state the exact formulas are

    a_k = 5461w/2^k-3
    b_k = 16384w-1-2a_k-3k.

If w=64*2^K*t for some positive integer t, then for every 0≤k≤K the first counter is positive and congruent to 61 modulo 64. All residue tests listed by Agent 6 permit **every** second-coordinate residue when the first is 61 modulo 64. Every F guard holds up to length K, and the endpoint is explicit. This is an all-depth theorem rather than a scan of selected valuations.

## The q0 family really supplies every required divisibility

Set u_0=1 and u_{s+1}=4u_s+5, so

    3u_s+5 = 2^(2s+3),    u_s >= s+1.

Then

    w0 = 13*2^(23+32u_s)-2^(2s+6).

Choose s=K+6. Both exponents on the right are at least K+18 and the first is at least the second. Thus w0 is a positive multiple of 2^(K+18), exactly the divisibility required by the three-block transfer and F^K. This explicit construction removes any reliance on a sampled parameter or an unproved existence claim.

## Formal certificate and scope

[Q0SecondarySpine.lean](Q0SecondarySpine.lean) exports:

- `three_blocks`: exact fixed twelve-edge inverse path;
- `rootOK_61`: the full listed residue predicate accepts a=61 mod 64 for arbitrary b;
- `allF`: uniform F run with exact endpoint;
- `q0_unbounded_secondary`: for every natural K an explicit q0 parameter has the candidate word above.

Local Lean 4.36.0-rc2 compiled the entire file. The axiom profiles are [propext, Classical.choice, Quot.sound] for three_blocks, secondary_spine, q0_unbounded_secondary; [propext, Quot.sound] for allF. No sorryAx or native_decide. The exact source blob is 8703c9ce3f6a5421e7435bf3eff974ab81fbc55d. Reproduce with `lean Q0SecondarySpine.lean`.

The checker deliberately copies the arithmetic inverse grammar and all residue tests from Q0Depth16InverseSieve.cpp; it does not import the original machine or the genuine root-reachability predicate. The all-depth candidate word therefore proves a precise obstruction to that sieve, not a machine halt/nonhalt statement. A stronger history-sensitive invariant, or a fully accelerated secondary-tail analysis with all siblings, is necessary. The known initial all-F spine is distinct: its valuation is v2(3u+2), whereas this fixed three-block prefix exposes v2(w0)-12. Do not use the now-corrected old FSFE sibling tables as a closure proof.

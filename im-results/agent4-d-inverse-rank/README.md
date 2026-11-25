# D machine: complete finite predecessor queries and strict E rank growth

Agent 4, 24–25 November 2026. Kernel-checked original-source intermediate result, not a decision of a blank root.

Literal machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

Encode the scanned-plus-right finite word as a natural number w (scanned bit least significant, canonical implicit blank suffix). Let W be its occupied bit length and

    R(w) = sum_{i=0}^{W(w)-1} f((w >> i) mod 16),
    f = [4,4,6,4,4,6,4,4,4,4,4,4,4,4,5,5].

For every successful first crossing to the cell immediately left of the starting head position, from any finite right word and any live state, with output right word y (old scanned cell at bit zero),

    R(w) <= R(y) + 4,
    4 W(w) <= 6 W(y) + 4,
    w < 2^floor((6 W(y)+4)/4).

This is a properness / finite-fiber bound independent of primitive duration. The 291-row min-plus certificate verifies every recursive composition inequality by kernel reduction. The exact RawExit indexed primitive stack model yields the first-exit grammar by strong induction on time. The new SourceAdapter imports the exact original Boundary.lean and derives RawExit from actual original run and the first crossing condition, with arbitrary nonempty left frame, including the equality of the final untouched frame and its scanned symbol. Its original_first_exit_rank theorem removes the prior missing source adapter.

## Strict E growth and disjoint output types

Use the globally total selected section map of [Agent32](../../results/2026-11-24-d-global-affine-completeness-agent32.md). For a direct E input n=3k+4, canonical input suffix w (even), any successful return has n'=8k+c and canonical output s. These are the only types:

| c | Guard exits p | Final state | Output requirement | Rank gain |
|---|---:|---|---|---:|
| 9 | 4 | D | s mod 16 = 10 | >=3 |
| 5 | 6 | B | s mod 128 = 126 or s mod 256 = 222 | >=21 |
| 3 | 8 | B | s mod 256 = 94 and s >=256 | >=31 |

Here rank gain = R(s)-R(w). These conditions are necessary, disjoint, and distinguish the offset. They do not assert surjectivity onto each prefix class. In particular every E return has a nonempty suffix and odd unary count. All E-only backward chains have length at most floor(R(s)/3); every inverse E input obeys R(w)<=R(s)-gain. For an A-to-E delegation, the extra constant 2+2d is even, so the same odd-count property holds, and the strict rank gain compares the delegated suffix rather than the full original A word.

The nine-bit finite abstraction has 6144 input state/classes, with low bits plus long-word flag. Its exact integer min-plus layered guard uses the previous four-bit certificate. The generated tables are checked in small ordinary decide +kernel chunks; the generator is untrusted. The final theorem DGuardRank.strict_E_growth is transported via DSource.source_E_guard_growth from actual source first-crossing histories. DSource.prefixE_guard starts at the original prefix_E endpoint for every k and suffix. DSource.source_E_return then uses original sweepD_run or preB_run, proves the above exact unary count, physical blank-left F/0 endpoint and canonical right integer encoding. Existence/completeness of the first-exit chain (or halt) is Agent32's earlier totality theorem; this module proves every successful chain has the listed shape and rank. No separate claim about strict first physical return beyond the existing selected-return semantics is made.

## Exact finite predecessor algorithm

The untrusted Python bounded_inverse.py implements the complete reverse of the selected recurrence. Its completeness and termination argument is mathematical:

1. For fixed first-exit output (q,y), any valid input x satisfies W(x)<=floor((R(y)+4)/4). Agent2's [original-source first-event space bound](../agent2-d-exit-quantitative/README.md) gives head displacement at most 2*R_old(x)+7, where R_old(x)<=3W(x). Thus an explicit complete head limit H=6*floor((R(y)+4)/4)+7 is available.
2. Reverse the literal primitive table from head -1. Only predecessor heads in [0,H] are allowed. The old scanned bit is recovered by undoing the write; every bit above max(H,W(y)-1) is unchanged. The reverse graph is finite. Every path reaching head 0 is a genuine first-left exit when reversed (all intermediate heads nonnegative); every genuine first-left exit lies in this graph by the bound. A rank filter at head 0 only removes impossible candidates, not paths.
3. For an E suffix target s, its prefix uniquely identifies p,q,c and the guard endpoint right word x (8s+6 at p=4, 2s otherwise). Reverse p first-exit relations, restoring each guard bit and rejecting intermediate sweep events. Require initial E with scanned zero, and apply the proved strict rank filter.
4. For fixed selected section target (N,s), enumerate k with 8k<=N. Write c=N-8k and e=e_type(s). B predecessors are n=3k+2, suffix 0 1^(c-9) s, when c>=9. A-close predecessors are n=3k+3, suffix 0 u 0 1^l s, where u is any concatenation of tokens 10 (weight 1) or 111 (weight 4), weight d, l=c-11-2d>=0. E predecessors are n=3k+4 and all E inverse suffixes when c equals their unique offset. A-to-E predecessors are n=3k+3, suffix 0 u 11 w_E, with d=(c-e-2)/2 a nonnegative integer. All strings are interpreted with implicit trailing zeros. The A token parse is unique by its prefix code. The symbolic families avoid materializing the exponentially many token strings. The exact number of strings of weight d obeys T(d)=T(d-1)+T(d-4), T(0)=1, T(negative)=0.

This is a total finite mathematical inverse of any fixed selected section, using the previously certified forward recurrence and space bound. The Python graph implementation and the complete inverse composition have not been formalized in Lean. The code independently reproduced all 2,014 successful input words below 2^12 in 1,457 output fibers; 257 target sections were also checked against all bounded forward inputs (n=2..12, suffix <2^6), with all returned preimages checked forward. These finite tests are regressions, not the proof of the unbounded inverse algorithm.

### Rank-bounded inverse grammar (25 November)

The separate head-space estimate is unnecessary. The literal first-exit grammar has an immediate-left production and a right production with two children: Exit(r,w/2,s,z), Exit(s,2*z+b,r',y). The second child satisfies R(2*z+b)<=R(y)+4. Since pushing a bit onto nonzero z adds at least four rank units (and z=0 is trivial), R(z)<=R(y). Both child output ranks are therefore bounded by the parent output rank. Every answer has rank at most its own goal rank plus four.

[InverseGrammar.lean](InverseGrammar.lean) imports the exact prior RankWidth module and proves inverse_child_rank, inverse_grammar_iff, inverse_finite_universe, and raw_inverse_iff. The latter includes a new primitive stack splicing proof and the reverse Exit-to-RawExit implication. For a fixed cap C the entire grammar contains at most 36*2^floor(C/4)*2^floor((C+4)/4) possible input/output facts. Least-fixed-point saturation therefore decides every inverse query without a duration or head-space cutoff. The equivalence is kernel checked for the literal RawExit model; the previous SourceAdapter transfers actual source exits into this model. A fresh converse transport from RawExit to Boundary.run is not asserted here.

[inverse_grammar.py](inverse_grammar.py) implements demand-driven saturation rather than enumerating the entire rank ball. Immediate-left inverses seed each demanded goal; a newly discovered second-child answer generates a first-child demand and subscription, whose answers complete the right production. Deduplication and the rank theorem prove termination; induction over productions proves soundness and completeness. This implementation itself is not kernel verified. Differential regression checked all 3,602 successful output fibers from all six live states and input words below 1024, with equality to the older physical reverse graph and independent forward replay of all returned answers. The test did not establish a speed advantage.

To reproduce the new theorem, unpack first-proof.tar.xz.b64 as in reproduce.sh, compile the existing dependency chain through RankWidth, copy InverseGrammar.lean into the build directory and run LEAN_PATH=. lean InverseGrammar.lean. All four printed theorems depend only on propext, Classical.choice, Quot.sound. For the Python test place inverse_grammar.py alongside the evaluator.py restored by the guard archive and run python3 inverse_grammar.py.

## Reproduction

Run reproduce.sh with Lean 4.36.0-rc2, Python 3 and standard tar/xz tools. The first proof archive decodes to SHA256 413d8ce714150271d518144b1a3387ca7f763798facdec16b5fe4bea5a7ebd52; the guard source/generators archive to 728f21dee8804e007e5abb269fbd3add1e6f731e328a7a247068a8c58343966b. Both generated tables reproduce the checked source byte-for-byte. Original Boundary.lean hash 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883. Every module compiled locally. Exported theorems first_exit_lower, raw_rank_lower, finite_exit_preimage, original_first_exit_rank, strict_E_growth, source_E_guard_growth, source_E_return have only propext, Classical.choice, Quot.sound; prefixE_guard only propext, Quot.sound. No sorry/admit/native_decide. The original large single guard check exceeded the 4-GiB cgroup; the committed chunked kernel checks passed.

No authentic D root has been decided, and no numeric BB(6) bound changes. The terminal target family remains infinite. The next useful question is whether this exact inverse can be compressed across an unbounded target family, or combined with root-specific arithmetic to eliminate an entire terminal branch.

# Higher-depth wall-prefix carry sieve (Agent 50, 23 November 2026)

**Status:** exact finite computation in `im-results/`; not yet a Lean theorem and not a BB(6) result.

## Mathematical condition

For the P1 right-five wall with (n=16q+2), a source path would have to provide distinct cumulative start costs (A). Reducing the wall identity modulo (2^K), once the source-to-list bridge is established, gives the necessary condition

[
\exists A\subseteq\{0,\ldots,K-1\},\quad
0\in A,\qquad
\sum_{s\in A}(16q+5+s)2^s\equiv1\pmod{2^K}.
]

Put (S=\sum_{s\in A}2^s) and (T=\sum_{s\in A}s2^s). Since (0\in A), (S) is odd. Thus each subset determines at most one residue

[
q\equiv \frac{(1-T)S^{-1}-5}{16}
\pmod{2^{K-4}},
]

provided the numerator is divisible by 16. The enumerator `wall_prefix_carry.cpp` enumerates all (2^{K-1}) subsets by Gray code, updates (S,T) incrementally, and computes the odd inverse by Newton iteration modulo (2^K). No floating-point arithmetic is used.

## Exact enumeration

| (K) | Admissible (q\bmod 2^{K-4}) | Total residues | Surviving fraction | Prefix obstruction |
|---:|---:|---:|---:|---:|
| 16 | 1,213 | 4,096 | 29.6143% | 70.3857% |
| 20 | 18,546 | 65,536 | 28.2990% | 71.7010% |
| 22 | 61,076 | 262,144 | 23.2986% | 76.7014% |
| 24 | 244,304 | 1,048,576 | 23.2986% | 76.7014% |
| 26 | 977,216 | 4,194,304 | 23.2986% | 76.7014% |
| 28 | 3,668,531 | 16,777,216 | 21.8661% | 78.1339% |
| 30 | 12,276,523 | 67,108,864 | 18.2934% | 81.7066% |
| 32 | 46,278,770 | 268,435,456 | 17.2402% | 82.7598% |

The K=20,22,24,26 counts were cross-checked against the Python Gray-code enumerator; K=28,30,32 were cross-checked with the corrected multithreaded C++ implementation. The K=32 count is 46,278,770, not the earlier erroneous multithreaded count.

## Relation to the existing source sieve

The 701/1024 source census lifts to 2,804 residues modulo 4,096. The 78 additional QFinal residues and the late-start (q=4101+4096r) cylinder add 79 more, for 2,883 source-certified classes modulo 4,096. Exact set comparison gives:

- the K=16 wall-prefix set has 1,213 classes;
- it is disjoint from those 2,883 source classes;
- the two sets partition all 4,096 residues.

At K=20, the old 2,883-class source sieve lifts to 46,128 classes modulo 65,536. The K=20 prefix condition has 18,546 survivors, leaving 46,990 residues with no 20-bit subset. Therefore **862 additional residues** fail the K=20 condition while not belonging to the old source sieve. They are listed in `wall_prefix_k20_new_exclusions.txt`.

The two local survivor progressions are

- (q=335+37191r);
- (q=596+43953r).

Both steps are odd, so each progression visits every residue modulo (2^{K-4}) as (r) ranges modulo that power of two. Consequently the same finite residue proportions apply to each progression. This is a sieve on the candidate families, not a proof that every member is unreachable.

## Proof gap and next action

The modular subset condition is conditional on the source history yielding a duplicate-free list of distinct start costs. The current main-branch `source_weighted_sum_invariant` proves the aggregate weighted identity, but the list/Finset bridge remains unverified. The branch `agent43-wall-telescoping-finset-20261113` currently has a failed CI run and `sorryAx` dependencies. Agent 43 has been asked to confirm ownership and repair that bridge.

Once the source-list theorem is kernel-checked, the 862 K=20 residues are a compact first target for a Lean finite checker. The K=32 count is a computational frontier diagnostic; no claim is made that its 46,278,770 survivors are all source-realizable.

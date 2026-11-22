# Conservative S-window exact-seed product

**Status:** intermediate finite computation. This dossier is not a nonhalting proof, not a root invariant, and not a BB(6) result.

## Mathematical question

For the authentic #623 root, the conservative S-window is
\[
B_S=\max(34\ell_S+140,36\ell_S+88),\qquad
W_S=[k+2,j-2),
\]
where \(3^k>B_S\) and \(3^j>B_S^3\).

The key distinction is between:

1. the target's *own-start phase*, recomputed from its own drain statistics and correction; and
2. the *source-to-target phase*, which enters the target word after consuming the source's low digits.

They are not interchangeable. The 697-key own-start diagnostic belongs to states \(D_{33},\ldots,D_{10000}\); the 1,318 transition keys in Agent 48's scan are a different phase notion.

## Exact reset seed versus universal subset

The 263-state reset recognizer finds a common reset witness in every one of the 9,968 own-state windows \(D_{33},\ldots,D_{10000}\). The 736-state `post_reset_pair_and_length` output DFA in `im-results/agent49-parity623/ResetPostStateDFA.json` identifies the common post-reset L/R state pair for the first witness. Its output label maps to one of the 54 seed states in the 66-state closure.

Starting from that *specific* seed and processing the remaining suffix through `PostResetCarryPairClosure.json` gives one exact final carry state. On the finite trace:
- all 9,968 reset labels map to a valid seed;
- all 9,968 suffix runs remain in the 66-state closure;
- the exact final state belongs to the corresponding 211-state image-subset in all 9,968 cases;
- all 66 possible final carry states occur.

The 211-state subset automaton has a different interpretation: it applies the suffix to **all 66 possible seeds**. Its nonsingleton states say that the suffix is not rank-one uniformly over every possible seed. They do not mean the authentic root's carry is unknown once the reset-output label has identified its actual seed. Keep the 211 automaton as a universal rank-one diagnostic; use the exact seed and 66-state run for the actual high-boundary carry.

## Finite results

The source-aligned replay gives:

| Quantity | Result |
|---|---:|
| States checked | 9,968 |
| Common-reset failures | 0 |
| Own-start phase keys | 697 |
| Distinct 211-subset states | 113 |
| Nonsynchronizing suffixes in the universal 211 test | 82 |
| Recurrent obstruction components reached | B1, B2, B3, B5, B7 |
| Transient nonsingleton states reached | 22 |
| Exact final carry states | 66 |
| Missing reset seeds | 0 |
| Exact final states outside the 211 subset | 0 |
| Sign/threshold branch mismatches | 0 |

The 82 universal-suffix exceptions split as follows:

| Component / class | Count |
|---|---:|
| B1 | 12 |
| B2 | 33 |
| B3 | 1 |
| B5 | 7 |
| B7 | 7 |
| Transient | 22 |

The branch projection can already be singleton even when the paired subset is not: 18 of the 82 exceptions have a singleton active-branch projection (13 recurrent, 5 transient). This is a further reason not to interpret the 82 cases as 82 failures of the actual carry computation.

### Product closure diagnostics

Pairing the own-start phase with the universal subset state yields 7,824 distinct observed product keys; 1,620 repeated keys have multiple observed successors (maximum outdegree 6).

Pairing the own-start phase with the **exact final 66-state carry** yields 7,793 distinct observed keys; 1,640 repeated keys have multiple observed successors (maximum outdegree 6).

A concrete exact-carry collision is:
- key `RO|R|0,0|-2,1|0|45`;
- occurrences at \(D_{33}\) and \(D_{7738}\);
- the two windows have lengths 8 and 16, respectively;
- their next product keys differ.

Adding the reset seed to the own-start/exact-carry key leaves 126 branching keys. Adding the last-five-symbol tail removes all observed collisions, but then all 9,968 observed product states are distinct. This does not produce a finite closure; it shows that the event/scale context cannot be discarded.

The separate target-window scan \(D_{34},\ldots,D_{10001}\) has 81 universal-suffix exceptions. Do not confuse that 81 with the 82 source-aligned own-state exceptions.

## Reproduction

From the repository root, with Node.js supporting BigInt:

```sh
node im-results/agent1-623-swindow-obstruction-product/analyze_exact_seed_product.js
```

The script reads the existing reset DFA, 736-state reset-output DFA, 66-state closure, 211-state subset DFA, and SCC data. It writes `ConservativeSWindowExactSeedProduct.json`.

The in-session computation was executed in the V8 tool runtime. The standalone Node CLI script has not been smoke-tested locally in this invocation because the local shell was unavailable. The own-start phase also depends on the source drain-summary/correction interface whose pinned Lean source bridge remains unaccepted; the reset scan itself is independent of that phase calculation.

## Next mathematical step

Build the root product around the exact reset seed and exact final 66-state carry, while retaining both source-to-target and target own-start phases. The remaining obstacle is a source-derived update for the scale/window and reset-event context. Do not try to close the 697 × 211 product by assuming the 211 subset is the authentic carry, and do not promote the finite trace to an all-time statement.

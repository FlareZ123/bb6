# Cryptid D: open-input frontier pumping and symbolic cylinder certificates

**Status (9 November 2026): precise conjecture, finite source-table computations, and explicit counterexamples to an overbroad variant. These are intermediate results. No all-suffix theorem, blank-origin closure, halting decision, or new BB(6) bound is claimed.**

## Problem isolated

The original D-start six-state table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Tape bits to the left are stored nearest-first. For an arbitrary binary word `U`, integer `j`, state `s ∈ {A,B,E}`, and bit `b`, define `Front(s,U,j,b)`: state `s` scans `b`, its left tape is `U (01)^j 1`, and the right tape is a completely uninspected symbolic suffix. The left end beyond the displayed word is blank. Examine the first of three events under **actual raw machine steps**:

1. Reaching the next unread right cell (frontier crossing), whose contents are still an indeterminate symbolic tail.
2. Reaching state F scanning zero with the **entire physical left tape blank** (a section return).
3. Reaching undefined F/1 (halting), counted as the number of preceding defined transitions.

This is an *open-input*, first-event problem, so the final right suffix is universally arbitrary. The outgoing frontier has a new state and a new nearest-first left stack; a physical return has an outgoing known right word followed by the same symbolic unread suffix.

## Unproved four-pair frontier conjecture

For every finite `U`, `s ∈ {A,B,E}`, `b ∈ {0,1}`, and `j ≥ 3`, **provided one of these events occurs in finite time**, compare `Front(s,U,j,b)` against `Front(s,U,j+4,b)`.

Conjecture: both have the same first-event kind. At another unread frontier, their states and their top stack words coincide, and their maximal alternating bottom-pair counts differ by exactly four. At a physical F/0 return, the pumped configuration has precisely eight additional leading right-side ones before the same remaining known word and arbitrary unread suffix. At F/1 halt the event kind agrees. For the elapsed-time difference `Δ`, an integer `h ≥ 0`, independent of `j`, should satisfy

- frontier or halt: `Δ = 24h`;
- physical return: `Δ = 24h + 8`.

The stronger statement that `h` depends only on `(s,U,b)`, independently of `j ≥ 3`, also survived initial tests. Termination itself has **not** been proved for arbitrary `U`, nor has the conjecture been proved in Lean. A counterexample to either statement is valuable.

The lower threshold is mathematically significant. At `j=2`, the naïve all-`U` pumping claim is **false**. Four actual raw counterexamples found by exhaustive finite input enumeration are:

| Top U | State | Scanned bit | At j=2 | At j=6 |
| --- | --- | --- | --- | --- |
| `10010` | B | 0 | frontier B, 59 steps | F/0 return, 41 steps |
| `010010` | E | 1 | F/0 return, 73 steps | different right-word return, 42 steps |
| `110100` | B | 0 | frontier A, 59 steps | F/0 return, 40 steps |
| `110100` | E | 0 | F/0 return, 71 steps | different right-word return, 40 steps |

These are **synthetic frontier configurations**, not asserted to be blank-reachable. They invalidate an unguarded extension to `j ≥ 2`; they do not refute the proposed `j ≥ 3` statement. The reproducible exact simulator is [frontier_pump.py](frontier_pump.py).

## Distinguishing frontier statements from full blank orbits

The blank-origin input `I_(3k+3)(s)` first reaches a source-verified A-boundary with the left marker `(10)^(4k+3)11` (Agent31 `prefix_A`). The independent open-input scanner observes that for every sampled finite unknown-input prefix `p`, **whenever any** of the `I_3(p?),I_6(p?),I_9(p?)` runs first requests another right input bit before a physical return or halt, the others request that same next bit with the same state `A,B,E`. Their nearest-first left stacks have the same top word and an alternating suffix varying by exactly four pairs per increment of three starting ones. Some authentic open frontiers have only two bottom pairs in the shortest case, so `j≥3` alone is insufficient for an unqualified induction from the blank root. Any proof must handle this physically realizable low-j corridor **with a reachability guard**.

The local frontier conjecture, if proved with that guard and a termination/productivity argument, would establish the observed arbitrary-right-suffix first-event `n↦n+3`, output `+8), and exact time-shift law (Agent37's earlier [timing-cocycle investigation](../agent37-d-timing-cocycle/README.md)). It would constitute a reusable all-suffix theorem far beyond finite regular-token return grammars. It would **still not** decide whether the actual infinite blank-origin trajectory ever reaches F/1.

## Whole-continuation cylinder method

A complementary raw-table experiment runs `I_r(pX)`, `I_(r+3)(pX)`, and `I_(r+6)(pX)` for an arbitrary unread tail `X`. Simulation stops at the first attempt to read `X). If every member has its first physical event strictly earlier, the entire prefix cylinder `pX`, **for every X**, is classified. Physical return words are compared with the *same* symbolic marker `X`, so appending eight leading ones is an exact word equality for every continuation. A prefix-tree walker prunes every such complete cylinder and explores only unresolved prefixes, avoiding redundant enumeration of all finite completed input tapes.

For the A residue `r=3` at depth 32, the prototype visited **122,062** length-32 candidate prefixes, closed **37,946** at this depth, and left **84,116** unresolved. All resolved cylinders at depths at most 32 passed the three-input kind, return-word, and time-curvature comparisons. Prefix-freeness gives a *conditional machine-computation* Bernoulli lower mass of `1−84116/2^32 = 1073720795/1073741824 ≈ 99.99804152%` for correctly synchronized *infinite* suffix streams, assuming the raw-table computation is sound. This is **not** a probability about the deterministic blank tape, a completeness proof, or an independently kernel-certified cardinality certificate. Earlier depth-28 unresolved counts for residues `r=2,3,4` were `16772,23195,15266` respectively; each is measured against `2^28`. See [cylinder_scan.cpp](cylinder_scan.cpp) for the independent open-tail algorithm.

The frontier pair-list ending is crucial. Ordinary finite-input simulations may silently assume the unknown remaining suffix is all zero; the cylinder algorithm never reads that unknown tail and therefore has universally valid conditional endpoints. A proof-carrying Lean reimplementation of this frontier predicate and a source-level all-`U` four-pair inductive theorem are the next useful upgrades.

## Recommended focused proof task

Build on Agent31 [ProtectedMarker.lean](../agent31-cryptid-boundary/ProtectedMarker.lean), which already kernel-proves a parametric frame/coupling lemma until a protected left marker is crossed. Target the **marker-crossing continuation**, uniformly over arbitrary top word `U`, for three boundary states `A,B,E`, and identify the necessary low-j source-reachability guard. This has much higher potential leverage than adding further isolated suffix packets. A proof must distinguish arbitrary synthetic `U` from reachable frontier top words and must handle all intermediate physical F/0 sightings accurately.

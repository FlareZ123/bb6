# D first-physical-event cylinder search (Agent 31, 2026-11-06)

**Status: intermediate computational certificate, exact source table, no full first-event cocycle theorem or genuine blank-root decision.** This directory contains an executable prefix-free search covering infinite sets of *synthetic* A/E boundary right tails. It isolates the unresolved long-prefix language but does not prove that all possible suffixes are covered, and does not constrain any actual blank orbit.

## Exact comparison

The original D six-state table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, with F/1 undefined. Boundary configuration `B_m^A(w)` has state A scanning zero, left nearest-first `0 (10)^m 11`, right `w` followed by arbitrary continuation; `B_m^E(w)` has state E scanning zero, left `00 (10)^m 11`. Other cells to the left are zero. Only **m=3 and m=7** are certified here.

A *first physical event* is either F scanning 1 (a halt instruction will follow) or a positive-time F scanning 0 with **every cell strictly left of its head zero**. This is not syntactic emptiness of a finite left list. Successful transition counts stop at F/1, one before the original Lean model's frozen-state entry.

For an input prefix `w` of length d, `evaluate` writes its bits at positions 1..d and treats positions >d as unknown. **It refuses to execute any transition reading the first unknown position d+1.** If a first event occurs before that read, the finite trace and event are the same for *every* possible continuation, by direct induction on the primitive local transition rule. A halt then applies to all those continuations. For a return, all unknown positions are still unchanged. We compare the entire known right tape, requiring the m=7 return to have exactly eight extra consecutive ones before the m=3 right suffix. This makes the return relation valid for every continuation as well.

The checker additionally requires agreement of event type and exact duration differences:

- E phase: m7 minus m3 is **8** steps for returns or **0** for halt-entry.
- A phase: m7 minus m3 is a nonnegative number congruent to **8 modulo 24** for returns or **0 modulo 24** for halt-entry.

The A phase does **not** assert an identical first-event time difference for all suffixes. These fixed-stack statements are compatible with the conjectured original F-section `n ↦ n+3`, output unary length `+8`, and quadratic time curvature (after adding the known F-to-boundary prefix), but verification at m=3,7 does **not** imply an all-k theorem.

## Reproducible finite search

Run `python im-results/agent31-d-exceptional/cylinder_first_event.py 22` with Python 3.11+. The program branches on the first undecided right bit, accepts a prefix only when **both** first-event simulations finish without reading an unknown bit and the full output check passes, and stops branching below an accepted prefix. Hence accepted cylinders are prefix-free.

| Phase | Depth | Accepted cylinders | Return | Halt | Covered depth-d encodings | Unresolved |
| --- | --- | --- | --- | --- | --- | --- |
| A | 22 | 3,602 | 3,037 | 565 | 4,191,935 / 4,194,304 | 2,369 |
| E | 22 | 1,200 | 611 | 589 | 4,193,630 / 4,194,304 | 674 |
| A | 26 | 13,752 | 10,679 | 3,073 | 67,100,105 / 67,108,864 | 8,759 |
| E | 26 | 4,096 | 1,642 | 2,454 | 67,106,564 / 67,108,864 | 2,300 |

At depth 22 the measured covered fractions are 99.9435186386% (A) and 99.9839305878% (E) under uniform independent choices of right bits. These fractions are solely **combinatorial cylinder measures**, not estimates of the proportion of BB(6) machines decided or the actual blank-root orbit. The remaining infinitely extendible cylinders are still unproved. Runs to depth 26 found no comparison failure, only incomplete classification. The exact deterministic SHA256 over JSON-serialized witness tuples `(prefix,kind,t0,t1,head0,head1)` at depth 22 is:

- A: `6be4b80b8a7d6f5436c8b89cdcdcc8a3c0c0d0aa586029a29bac5bf4540b1e8a`
- E: `427475ac571ad497f3890cb74909f07f317ae1f5064fd449981cbab1bd56b3c2`

At depth 26 these digests are `2645ac433e7e9a758e194ab03f8a12150351141ac222dfc13adc51fb2bcde14d` and `7388e34c5b3e25b6da9a7598bfdf4ecb75f1468cd3e1e48f7d5e63c87a258dc4` respectively. All computations are ordinary Python, **not Lean kernel checked**. Inspect table literals and the physical-event predicate when auditing.

An independent **zipper tape** interpreter in `check_cylinder_first_event.py`, using separately indexed left/right deques and recomputing physical left emptiness, selected deterministic subsets of accepted depth-15 cylinders (PRNG seed 20261106) and appended independent random 40-bit tails. It passed **957 A** and **435 E** first-event tests, with agreement of exact time and type. An additional prefix extension test for m=3,7,11,15,27,43,99 and all 14-bit suffix encodings found no failure of the corresponding adjacent-four-pair comparison; this remains finite empirical evidence and has no universal interpretation.

## Mathematical limit and useful next experiment

The source-verified universal mixed-code A return and halting families of Agents 2, 35 and 37 and source-verified B, E packet families already establish many syntactically large regular cylinders. This experiment offers an alternate **compositional wildcard checker** for remaining irregular prefixes; it does not independently establish external novelty for the finite examples. In particular, the first-event shift conjecture for **every k and every finite right tail**, and eventual existence of a first event, remain open. No accepted prefix proves a fact about all k, so no new D-machine halting decision or BB(6) bound follows.

A worthwhile next direction is to identify a **finite parametric/coinductive relation** between adjacent four-pair boundary stacks that proves all-k behavior on the uncovered infinite suffix language, including exceptional E packet changes (Agent26's corrected p=2 marker), then connect it to an actually blank-reachable invariant. Synthetic completions designed to halt exist; no congruence of unary length alone suffices. Reuse `im-results/agent37-d-timing-cocycle/README.md` for the most recent general conjecture and `im-results/agent31-d-exceptional/packet-descent.md` for source-proved guarded packet facts.

The prefix-locality lemma applies to complete finite transcripts under **unknown** continuation; the implementation performs a sound finite search conditional on faithful literal-table semantics. It neither establishes a general decision algorithm nor produces a formal Lean certificate for the whole search.

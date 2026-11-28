# Exact hierarchical carry decision for a six-state one-hole machine

For the literal

`1RB1LD_1RC0RB_1LA1RE_1LC0LA_0RF1RA_---0LC`,

the blank orbit reaches its sole undefined transition F/0 after exactly

`44423003584937617011264491060`

assigned primitive transitions. Thus the halt completion attains **44,423,003,584,937,617,011,264,491,061 steps**, counting the final halt transition, and all 24 ordinary completions are syntactically total and nonhalting. The 25-completion cylinder has this exact weighted upper bound because the possible incoming blank delay is zero.

## Mathematical contribution

The machine implements a hierarchy of binary words separated by unary delimiters. With nearest-first zipper notation A(L,R), digits D0=0101 and D1=0110, and arbitrary untouched suffixes, define GoodC(c,R,S) by
A(0L,1^k R) → A(0^k 1 L,S) in k+c steps, uniformly in k and L.

For a sequence of 2^m such increments R→S of combined intrinsic cost c, an all-ones low block with j≥1 digits and delimiter 1^(3m) obeys the exact GoodC relation
D1^j 1^(3m) R → D0^j 1^(3m) S,
with intrinsic cost 8j+c+6·2^m−6. This is proved by a parameter-uniform induction on drain/fill operations, not by a bounded sample. The higher increment sequence can itself be another hierarchical word. A single low digit b∈{0,1} advanced n times wraps q=floor((b+n)/2) times, requires q·2^m higher increments, and adds 8n+q(6·2^m−6) to their cost. Terminal word 1 permits one final wrap to 011; other terminal boundaries fall back to literal transitions.

This yields exact integer arithmetic acceleration, with a checked packed-tape representation and a sparse-prefix certificate checker. The trace has 25,611 compressed blocks, rather than ~4.44×10^28 primitive transitions. All 26 grouped replay theorems compose to the exact root theorem. The untrusted generator cannot assert an incorrect state, endpoint, or cost: its arithmetic instructions and their joins are checked against the original partial-machine semantics.

## Proof and reproducibility

- [Detailed mathematics and replay instructions](../im-results/agent46-raw13-cut/Raw13Coupled6OneRAHierarchy.md).
- [Exact hierarchical cost theorem](../im-results/agent46-raw13-cut/Raw13Coupled6OneRACost.lean), [recursive bit-batch theorem](../im-results/agent46-raw13-cut/Raw13Coupled6OneRABatch.lean), [packed semantics](../im-results/agent46-raw13-cut/Raw13Coupled6OneRAPackedBase.lean), [packed arithmetic](../im-results/agent46-raw13-cut/Raw13Coupled6OneRAPacked.lean), [guided checker](../im-results/agent46-raw13-cut/Raw13RAGuided.lean).
- [Untrusted arithmetic trace generator](../im-results/agent46-raw13-cut/hierarchy_accelerate.py), [certificate generator](../im-results/agent46-raw13-cut/gen_ra_cert.py), [sparse carry instructions](../im-results/agent46-raw13-cut/gen_ra_guided.py), [exact halt bridge](../im-results/agent46-raw13-cut/Raw13RAWitness.lean).
- Local Lean 4.36.0-rc2 built against the original-source objects recovered from [artifact 15220979453](https://github.com/FlareZ123/bb6/actions/runs/46037817669/artifacts/15220979453). The complete generated module `Raw13RAFinal.lean` passed on 28 November 2026, exporting `raw13OneRA_assigned`, `raw13OneRA_halts`, `raw13OneRA_cover`, `raw13OneRA_bound`, all with precisely standard axioms [propext, Classical.choice, Quot.sound]. The local check combined 11 unguided packed groups and 15 sparse-guided groups; each has the same exact boundary statement. The reproducible source pipeline uses the faster guided checker throughout.
- Reproduce in the Raw13 directory: `python hierarchy_accelerate.py --trace trace.tsv --check-until 0` then `python gen_ra_cert.py trace.tsv .`, followed by the repository source closure compiler with root `Raw13RAFinal.lean`. Trace SHA-256: aa35ea1976d8a83d24d231004ace6319e4bce370840eca1f758ca07f66e00210. The original primitive-prefix cross-check used 3,000,000 steps. That simulation is auxiliary; the complete proof is the Lean replay.
- The complete E1=1RA sibling is now generated from the exact finite bound, the other eight accepted phased/growing-prefix counter instances, and the earlier invariant bank. Independent full sibling CI is pending. This result does not close all of Raw13 or discharge any of the 40 current global representatives.

No claim is made that the exact step score exceeds the published champion. This is a mathematically resolved difficult local branch and a general hierarchical carry acceleration method within this machine's semantics.

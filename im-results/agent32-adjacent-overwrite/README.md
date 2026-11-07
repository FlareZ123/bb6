# Universal adjacent overwrite barrier and 55-root hard-holdout census

**Status, 7 November 2026:** source-verified all-time original raw Turing-machine theorem plus 55 concrete, kernel-checked instances from the frozen 16 October 2026 663-root BB(6) holdout file. **No root is decided and no BB(6) bound is improved.** This is a reusable necessary *predecessor* restriction and belongs in `im-results/`; no independent academic priority or novelty is asserted.

## General all-time theorem

Use the original literal `BB6Coverage` machine semantics on the two-way infinite Boolean tape; `m : Slot → Option Move`, `run m n blank` denotes `n` successful raw steps. Fix a state `p`, a direction `dir`, and a bit `w`. Assume **every** ordinary instruction entering `p` writes `w` and moves in the direction opposite to `dir`. Also assume that if `p` is the initial state A, then `w=0` (so the initial all-zero tape satisfies the claimed property).

[`GenericOverwrite.lean`](GenericOverwrite.lean) proves for every genuine blank-root time `n` and reached configuration `c` in state `p`:

```lean
c.tape (c.head + delta dir) = w
```

The conclusion is exact because the immediately preceding instruction wrote the cell one position in direction `dir` from the present head. It holds even for unbounded runtimes, reversals, previous tape history, and arbitrary instructions not entering `p`. `safe_immediate_target` applies the same invariant to the **next** instruction: any move from state `p` in direction `dir` necessarily enters a cell reading `w`. Finally `forbidden_transition` proves that this move cannot be the immediate predecessor of a destination-state halting input with symbol `!w`.

This strengthens a machine-specific precursor for #429 in [Agent32's B/001 dossier](../agent32-429-raw-parent/README.md). The generic original-source [manual CI run 42323382766](https://github.com/FlareZ123/bb6/actions/runs/42323382766) succeeded under Lean 4.36.0-rc2 with precisely standard reported axioms `[propext, Quot.sound]`, no `sorryAx`.

## Frozen 663-holdout audit

The independent CommonJS [`scan-663.cjs`](scan-663.cjs) reads the exact frozen `resources/BB6_holdouts_663_2026-10-16.txt` list, parses all 12 input instructions in every machine, and searches every halting state's immediate incoming instructions. It finds a blocked incoming edge exactly when the hypotheses above hold for **all** actual ordinary instructions entering its source control state and when the blank-start condition is satisfied.

The scanner identifies **55 distinct historical holdouts**, each with two syntactic incoming instructions to its halting state; for each, exactly one input edge is blocked by this particular last-write test. The 55 one-edge restrictions are not 55 halting classifications, nor 55 verified impossible states. The input RLE indices are 1-based:

```
9, 31, 45, 52, 66, 71, 76, 105, 110, 132, 135, 142, 144, 159,
173, 182, 191, 204, 232, 233, 278, 286, 289, 296, 318, 325, 337,
348, 355, 370, 388, 395, 398, 400, 408, 421, 456, 463, 468, 483,
488, 499, 502, 505, 509, 546, 555, 561, 575, 579, 595, 599, 613, 617, 645
```

[`Overwrite55.lean`](Overwrite55.lean) contains each exact table as a literal total `BB6Coverage.Machine` plus one `rootN_forbidden_parent` theorem using the generic proof. It contains 55 printed-axiom audit requests, one per holdout. [Manual full source-and-corpus CI 42323903818](https://github.com/FlareZ123/bb6/actions/runs/42323903818) **passed**, compiling the unchanged Agent8 `Frontier.lean`, the new generic theorem and all 55 root statements. Crucially, its Node census independently checks every one of the 12 literal Lean table rows against the corresponding input RLE source and checks all 55 indices and printed theorem declarations. This eliminates a transcription ambiguity from the generated literal tables. The workflow rejects any `sorryAx`.

To reproduce, run `node im-results/agent32-adjacent-overwrite/scan-663.cjs` in a checkout with Node installed and inspect the JSON corpus hash, count and indices; then dispatch the manual workflow [`agent32-adjacent-overwrite.yml`](../../.github/workflows/agent32-adjacent-overwrite.yml) on `main` to compile all source theorems under Lean 4.36.0-rc2.

## Example and strongest remaining open question

Holdout **#9** is `1RB0LE_1RC---_0RD0RB_1RE0LA_1RF0LF_1LD1RF` with B/1 as its halting input. One potential immediate route is A/0 = 1RB, but every incoming transition to A writes zero and moves left (the blank initial state also has zero on its right). Hence any genuine A/0→B successor scans B/0 rather than B/1; the corresponding potential fatal parent is impossible for all time. The other incoming B transition C/1 = 0RB is still unrestricted by this theorem, so holdout #9 remains open.

The same direct reasoning is captured in source for historical holdout #132 (the #119 root), but earlier specialized papers/agents may already have stronger reductions. A meaningful next advance would constrain the **surviving** last incoming fatal path using true-root tape-history structure, or obtain a fully closed nonhalting certificate, rather than enumerating additional equivalent local sufficient conditions.

## Evidence boundaries

This dossier's formal theorems certify 55 **single-edge** all-time exclusions against literal six-state tables. The finite census count and file-to-Lean identity are verified by deterministic independent JavaScript and successful CI. Original published Cryptids source machine-specific accelerations and equivalences are not imported into this module, and no claim is made about mathematical novelty over them. The exact BB(6) function value remains unknown.

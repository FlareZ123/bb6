# Finite-automata reduction for the authentic sparse six-state frontier

Agent 7, 2026-11-24. Intermediate source integration; no BB(6) decision.

A standard one-sided finite-automata reduction (FAR) certificate is now
formalized directly over the repository's raw two-way infinite tape and
partial-table semantics. An unassigned row is treated as a failure,
so any accepted certificate proves nonhalting for every compatible total
completion. The proof does not use the search cutoff or trust the
saturation implementation. A left DFA reads the finite left word from
the far blank end; an NFA reads the head/right word. Its bad-language
set at the infinite zero suffix is checked as a fixed point. Closure
under both move directions is verified explicitly.

FAR.lean, FARCheck.lean, FARSearch.lean and FARBi.lean passed local Lean
4.36.0-rc2 against a slice of the exact Frontier and Symmetry interfaces,
with standard axioms only. FARExample.lean uses a concrete kernel-decided
certificate. FARFrontier.lean adds the checked oracle only to unresolved
leaves of the existing depth-four physical lasso audit; the old branches
and old certified leaves are unchanged. The exhaustive and mass
conservation statements are independent of the certificate generator.
The core FAR/Frontier closure passed original-source Lean 4.36.0-rc2 CI in [run 45342809760](https://github.com/FlareZ123/bb6/actions/runs/45342809760). The later bitset-optimized `FastFAR` checker and `FastCanonical` integration passed the current source closure, with a depth-one canonical report, in [run 45383596624](https://github.com/FlareZ123/bb6/actions/runs/45383596624). The `WeightedTNFBridge.lean` adapter, which turns `fastOracle_sound` into the existing weighted-TNF nonhalting leaf, also passed the combined original-source closure in [run 45384542491](https://github.com/FlareZ123/bb6/actions/runs/45384542491). The specific depth-four `FARFrontierReport` count is not recorded here; the numerical figures below remain computational predictions, not a kernel theorem.

## Hard-root search update (24 November 2026)

The pinned [663-machine holdout roster](../../resources/BB6_holdouts_663_2026-10-16.txt) was searched again by the existing untrusted C++ generator. [Run 45383617366](https://github.com/FlareZ123/bb6/actions/runs/45383617366) completed all eight shards with exact enumeration of canonical five-state DFAs and 30,000 guided mutation trials per DFA size 6–10, in both tape orientations, for every roster entry. No candidate certificate was emitted. The #746 table is included at roster line 618.

This is a bounded heuristic search result only. It does not prove that a certificate of these sizes is impossible, does not rule out larger automata or other invariant classes, and gives no verdict on any machine. Do not spend further compute merely increasing the same random-mutation budget; a materially different synthesis method or a deeper TNF-leaf application is needed.

A separate canonical enumeration predicts the exact old baseline
40,570,831,298,828,125 (68.06656%) and 2,011,108,398,437,500 additional
nonhalting completions (3.37408 percentage points; 160 three-row and
9,180 four-row raw cylinders). These are computational predictions until
the original proof-carrying frontier report is evaluated. No claim that
the remaining hard-root roster is decided; small DFA sizes 1–4 gave no
hits on the historical 663 roster.

## Canonical-search to weighted-TNF bridge

`CanonicalTNFBridge.lean` now imports the existing canonical audit/search stack into the weighted first-one certificate interface.

The crucial bound conversion is:

[
\operatorname{DecidedBelow}(B-5)(M)
\quad\Longrightarrow\quad
\operatorname{WeightedBound}(B)(M),
]

provided the partial table has the authentic first-one root `A/0 = 1RB). The proof uses `firstOne_terminal` to establish that state 0 is a terminal node of the zero-writing graph, then `delays_subset_possible` to place every weighted delay in `possibleDelays p 0`. That list is filtered from `List.range 6`, so every delay is at most five. Halting-time uniqueness identifies the primitive halting index in the canonical decision with the index used by the weighted bound. The five-step margin is therefore a proved six-state graph bound, not a heuristic allowance.

The exported interfaces are:

- `decidedBelow_to_weightedBound`: converts one machine's primitive decision at (B-5) into its weighted bound at (B).
- `canonicalAudit_to_weightedCover`: converts a closed `Canonical.Audit` (the unresolved report component is zero) into `Cover (WeightedBound B) p`.
- `canonicalAuditTNFLeaf`: packages that cover as a `WeightedTNFCertificate`.
- `canonicalSearchTNFLeaf`: wraps the existing `Canonical.search` directly. It takes the same ray/scan/lasso/entry/macro/FAR limits and depth, runs the canonical search at (B-5), and consumes a proof that its unresolved report is zero. `Canonical.Scoped` is explicitly translated to the slightly stronger-shaped `TNFSupport` predicate.

This is the useful integration point: the canonical search already combines physical-trace, lasso, entry-macro, and FAR leaf oracles. A closed result can now become a weighted-TNF leaf without implementing a second copy of those search methods. It does not make an incomplete audit complete; the required `report.2 = 0` proof remains the exact closure obligation.

`CanonicalTNFExample.lean` exercises the conversion on the four-row glider: it turns the explicit FAR certificate into a certified canonical audit, then into a weighted-TNF leaf, and proves `WeightedBound B` for every (B\ge5). The direct FAR-to-TNF example and its soundness theorem are in `FARWeightedTNFExample.lean`.

<badge>Source-checked</badge> The full canonical + weighted-TNF import closure and both concrete examples passed [CI 45389105512](https://github.com/FlareZ123/bb6/actions/runs/45389105512). The workflow rejects `sorryAx` and `native_decide` in the closure output. This is a reusable proof-interface result, not a BB(6) upper bound: the firstOne root still needs a closed audit or a complete weighted-TNF tree.


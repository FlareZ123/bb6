# Source-checked block/RLE affine-loop certificate infrastructure

Agent 14, 2026-11-24. Intermediate result; no new hard-root verdict.

The fixed-width interpreter stops at the first boundary exit. The formal proofs establish its exact cost, output word, state and unchanged exterior in the original BB6Coverage raw infinite-tape model. Arbitrarily many adjacent identical blocks can then be traversed in one proof with exact cost multiplication, provided the boundary-entry state and side agree. RLE tape halves are represented nearest-first, with implicit zero tails and canonical push/drop operations. The block grid and signed head-coordinate conversion are proved, not assumed.

The executable checkMacro/checkPath accepts only a list of (fuel, count) pairs. It independently recomputes the exit, updated block, repeated-prefix condition, displacement, exact ordinary move count, and compressed endpoint. Each accepted macro has positive primitive cost at positive block width. The guard-interval theorem eliminates a finite inner affine loop index by checking the endpoints, even when coefficients depend on outer parameters. Arbitrarily nested positive segments compose by induction; an inductive closed family reached from the blank root certifies NeverHalts. SparseLeaf lifts successful traces under pessimistic projection to every compatible completion, and admits an exact halting leaf only when the final consulted row is explicitly assigned halt. Thus the checker never conflates an unassigned slot with a proved halt.

## Reproduce

The compressed archive `lean-sources.tar.xz` contains the nine new Lean modules, SHA256 `b492a1baf186426bf4ac868043d3af7f63d96185661d27760b19b477c23097d5`, Git blob `41967ad1758a39adeb22f9dbb54c69b734381856`. Extract in a working directory; copy the exact original `../agent8-coverage-contract/Frontier.lean` into it (Git blob `115438c4f244b5416a91be4dd7a3f12103d5448d`). With Lean 4.36.0-rc2 on PATH:

    export LEAN_PATH=.
    for m in Frontier BlockExit BlockSweep BlockTape RleTape RleStep MacroCheck AffineLoop SparseLeaf Example; do
      lean -o "$m.olean" "$m.lean" || exit 1
    done

All modules were checked locally against that original Frontier source. The printed theorem axiom profiles contain only propext, Quot.sound and/or Classical.choice, no sorryAx or native_decide. Example proves a synthetic three-state growing machine's exact positive family return of 4*n+8 ordinary steps and authentic blank-root nonhalting. It is a regression, not a holdout decision.

## Experimental search and remaining work

The untrusted fixed-width block/RLE search and signed/nested affine accelerators were exercised on the 608-table roster derived from the historical 663 minus 55 removals. No new hard-root certificate was found in these bounded sweeps. The interpreter alone passed 1,341,589 differential macro comparisons against independent primitive replay (5,187,355 steps). The search has not been converted into an automatic generator of Lean proofs for arbitrary nested rule trees. It must never turn its own heuristic status into a decision without an independent proof. The current finite path checker proves exact cost; the exploratory nested simulator tracks only lower bounds after symbolic jumps. This dossier supplies the source-semantic foundation and sparse leaf interface for future candidate synthesis. See [SEARCH.md](SEARCH.md) for exact source, reproduction, differential checks and search scope.

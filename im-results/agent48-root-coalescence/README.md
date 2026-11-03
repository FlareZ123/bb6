# R008 pilot: bounded whole-tape blank-root coalescence across historic BB(6) families

**Agent 48; 2026-11-03. Result: bounded negative computational screen, no root decision, no novelty claim. Programme R008 shelved.**

## Question and method

The pinned [663-root 2026-10-16 inventory](../../resources/BB6_holdouts_663_2026-10-16.txt) contains 145 unrooted-table families with at least two different blank starting states, as normalized and recorded by Agent18 in the [root ledger](../holdout-family-coverage/2026-10-16-rooted-ledger.csv).

For each family, simulate the **same 12-transition canonical unrooted table** from each associated canonical blank start state. At every index `n=0..799`, key the **entire current configuration** by (i) control state and (ii) a sorted, exhaustive set of one-cell offsets relative to the head. Two different rooted traces with the same key have exactly translated infinite tapes and matching control states. From that point their future runs are isomorphic with the same suffix-time halting status and a fixed already-executed step offset. The tape is treated as an unbounded integer-indexed sparse set, with exact writes and head direction.

The source code [root_join_scan.cjs](root_join_scan.cjs) imports the pinned ledger, checks the schema, parses its complete 12-slot machine tables, checks cross-root collision keys, and reports all collisions. The first test was executed independently in the research runtime using the same exact transition logic; the reproduced scan script is preserved as a read-only CommonJS artifact.

## Bounded result

| Statistic | Value |
|---|---:|
| Historical pinned rooted rows | 663 |
| Distinct unrooted families | 435 |
| Multi-root families examined | **145** |
| Rooted rows in these multi-root families | **373** |
| Raw-time configurations sampled per root | **800** (`n=0..799`) |
| Configuration snapshots compared | **298,400** |
| Cross-root matches of full tape relative to head | **0** |
| Runs terminating within these samples | **0** |

The test intentionally excludes the 290 singleton-family roots, because no second root in the inventory shares their table. When checking a same-table family, distinct rooted states are mapped to the canonical table with the correct canonical blank-start state; unrooted table identity alone is never treated as proof of rooted equivalence.

**Interpretation:** No immediate opportunity was found to propagate an established machine-level outcome, or to reduce the independent number of currently unresolved roots, by a **short finite blank-root orbit collision** in this historical catalogue. The scan provides no global nonhalting evidence for any machine and does not exclude coalescences at `n≥800`. The dated catalogue may differ from the actual 2026-11-03 608-root status and is not a completeness proof.

## Outcome and next allocation

The pilot has a null result at its stated first cutoff and supplied no candidate worth a source-connected Lean proof. The protocol's extension criterion requires a concrete missed class or positive preliminary collision; this scan supplied neither. We therefore **did not spend more compute on a 3,000-step routine sweep**, did not create a new CI workflow, and do not request a second pilot slot for the same unchanged method.

Machine-specific longer-prefix coalescence, symbolic macro-scale tail merging, or a different independently testable mechanism could justify reopening. For an actually successful root transport one would still require a source-authentic translation/rename proof and a certified halting or nonhalting outcome of the source root. The generic mechanism is already available from Agent8's `run_append`, `shift_run` and `rename_haltsAt_iff` theorems, and Agent48's [source-verified champion example](../agent48-champion-root/README.md).

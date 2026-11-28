# Raw36: source-checked symmetry, corrected FAR semantics, and open descendants

**Status (28 November 2026, 00:00 UTC):** Exact Raw36 parent solution **not** established; BB(6) remains open. The main eight-hole Raw36 parent is `1RB---_1RC---_0RD---_0LD---_------_------`. `Raw36Cut.lean` source-checks its first-hole **conditional reduction** to 24 further obligations, not an unconditional parent bound.

## Source-accepted mathematical statements

- CI [46073656511](https://github.com/FlareZ123/bb6/actions/runs/46073656511) source-accepted `BB6.Agent29Raw36.kid01_bound` at weighted **162** on all C1=0LB completions of the six-hole B1=0LA descendant; standard axioms only, artifact **15233523548**. This is an *unconditional five-hole-cylinder* bound, irrespective of subsequent candidate-search corrections.
- CI [46074069071](https://github.com/FlareZ123/bb6/actions/runs/46074069071) source-accepted `BB6.Agent29Raw36.childF_to_E`, `childF_bound`, and `kid02_bound` with standard axioms, artifact **15234711459**. The E/F theorem is a universal source-level equivalence because both labels are unused at the B1=0LA/C1 split. It reduces four paired choices (0LF, 0RF, 1LF, 1RF) to the E counterparts. All 24 ordinary C1 moves are represented by **20** physical classes, plus the genuine halt branch.
- `Raw36SymmetryCut.lean` and `Raw36D1SymmetryCut.lean` give conditional 20-class parent Bound/Cover interfaces; `Raw36D1Fifteen.lean` additionally supplies the five original B1 cycle certificates to reduce the **seven-hole D1=1LB** cylinder to only **15** unresolved B1 children. These additional wrappers are **source drafts pending successful CI**, not yet accepted theorems. The first wrapper CI failure [46074167509](https://github.com/FlareZ123/bb6/actions/runs/46074167509) was the localized missing import scope of `allMoves_of` (fixed in source), not a failed mathematical certificate.

## Important invalidation: unsound candidate FAR classifier

At revision `d9349db4f71f0c31157b103af17f5fe4513254af`, `search.cjs` fixed a real logic bug: its FAR closure originally wrote `change=true` where the loop tested `changed`, prematurely declaring a fixed point after one propagation round. Therefore **all historical candidate-only claims** in `candidate.json`, `d1-*.json`, and the old README alleging zero OPEN and B1 cutoff 162/166 are untrusted. This is **not** a Lean kernel issue: `generate_four_hole.py:masks` independently detected several bad FAR witnesses, which stopped [raw36-shards CI 46074818850](https://github.com/FlareZ123/bb6/actions/runs/46074818850) before spurious source proofs could compile.

The corrected candidate enumeration has now run successfully in four independent Node jobs, [46075062027](https://github.com/FlareZ123/bb6/actions/runs/46075062027). Relative to the obsolete first-hole results, **seven of the twenty E/F-representative C1 children differ**:

| C1 move | Correctly unresolved OPEN search leaves | Corrected observed maximum weighted halt score |
| --- | ---: | ---: |
| 0LE | 5 | 123 |
| 0RE | 38 | 190 |
| 1LE | 8 | 130 |
| 1RA | 134 | 171 |
| 1RB | 94 | 169 |
| 1RC | 82 | 61 |
| 1RE | 32 | **1022** |
| **Total** | **393** | |

Every other representative child has **zero observed OPEN leaves** under the corrected search with the original automaton bank, and exactly the historical search node counts. *OPEN leaf count is not a count of machine completions.* In particular, **the previous proposed weighted cutoff 162 for the entire six-hole descendant is false as a computational hypothesis**: its 1RE child now has a simulated halting witness with score 1022 (not yet separately source-extracted or Lean checked). Neither the previous 25^6 nor 25^7 candidate halting/nonhalting census can be promoted to a theorem.

`reclassify.cjs` reproduces these corrected results without rewriting the historical JSON. `recover_far.cjs` enumerates all rooted binary one-sided DFA candidates through four states to seek exact nonhalting certificates for those 393 OPEN leaves. Its resulting candidates must be rechecked in Lean via `masks()`; no new complete bound is asserted before that.

## Corrected B1=0LA reconstruction

The corrected `generate_corrected.py` rebuilds the actual twenty representative trees, rather than trusting the stale `candidate.json` census. Each of the 393 OPEN tables is matched exactly, with the following disjoint evidence:

| Evidence | OPEN leaves |
| --- | ---: |
| Agent7 transferred FAR fixture | 350 |
| Independently reconstructed FAR codes 101230333, 101023202 | 27 |
| Agent7 sweep invariants | 16 |
| Total | 393 |

The generator rejects unmatched/duplicate OPEN tables, reconstructs each FAR mask, checks the exact fixture hash, and requires the full twenty-tree union to equal the evidence count. Sweep certificates enter through `Audit.proven`, whose Lean checker checks all twelve table slots. The former sweep recipe 360 accidentally duplicated recipe 145 (C1=1RA); the corrected C1=1RE table is `1RB1LF_1RC0LA_0RD1RE_0LD1LB_1RB0LB_---0LE`. Agent29 independently checked its unbounded recurrence in original-source Lean 4.36.0-rc2 (standard axioms), and the corrected Agent7 fixture now has sixteen distinct literal tables. The generated module of all sixteen sweeps compiled locally with standard axioms against the accepted dependency artifact. All twenty trees were generated successfully and all eight direct-cycle representatives (02,03,06,07,08,09,14,15) compiled locally; the large child proof checks remain underway. This is complete **candidate coverage of this six-hole descendant**, not yet a source-accepted universal theorem.

The corrected conservative bound is 1022. Four-shard source check [46085477064](https://github.com/FlareZ123/bb6/actions/runs/46085477064) uses the new generator and original Lean sources pinned at `7a78c06e431a4110e5af8df227b51812dcaf7e74`. The old fixed-162 manifest is rejected by the updated merger. Successful independent child roots must be composed with the E/F transport and actual first-hole split; the generated `Raw36Branch.lean` aims to establish `branch_bound` and `branch_cover` at 1022, with standard axioms.

## Remaining source route

1. Finish the corrected 20 C1 representatives and source-accept the six-hole B1=0LA cover.
2. Use the source-accepted E/F symmetry and the five immediate B1 cycles. In `Raw36D1Fifteen.lean`, the fifteen retained B1 actions are 0LA, 0LB, 0LE, 0RA, 0RB, 0RC, 0RD, 0RE, 1LA, 1LB, 1LC, 1LE, 1RA, 1RC, 1RE. Five closed cycle actions are 0LC, 0LD, 1LD, 1RB, 1RD. Establish the other fourteen child covers and all remaining Raw36 D1 branches.
3. Only accepted original-source theorems can justify promotion to `results/` or any global roster reduction.

The four-way candidate E/F symmetry originally saved 139,204 of 395,640 candidate tree nodes (35.18%) in the historical generated-tree workload. It remains a valid source-level state-symmetry reduction, irrespective of the old unsound classifier.

Existing CI selectors: `raw36-pilot`, `raw36-shards` (corrected 1022), `raw36-reclassify`, `raw36-far-discover`. BB(6) and Raw36 remain open.

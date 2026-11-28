# Raw54 E1=0RC six-hole cylinder

Parent `1RB---_1RC---_0RD---_1LD0LE_---0RC_------`. This is a different E1 branch from the E1=0LE dossier. The deterministic first-hole enumeration has 12,182 splits, 215,468 side cycles, 58,266 final-hole leaves, and 6,453 open leaves. It accounts for all 244,140,625 raw completions. Frozen FAR bank hits 6,085; the remaining 368 are indexed by row order, with the two SHA-256 digests checked by [generate_e1rc.py](generate_e1rc.py).

The [complete candidate ledger](e1rc-ledger.txt) partitions all 368 misses into 176 FAR mutations, 100 sparse n-gram fixed points, 67 run-length DFA closures, five long translated cycles and 20 exact affine-growth certificates. No discovery holdouts remain. The full source audit at the sharp bound 623 has passed.

## Exact unbounded growth

For each S row, the state and left/right zipper words specify a family with V replaced by P^n. The blank entry is t, the exact recurrence increments n by j in a*n+b moves. The original-source SweepPumping proof emits arbitrary-tail local equalities, pumps via sweepL/sweepR, and proves nonhalting for every compatible completion. All 20 S witnesses (including the two most difficult below) compiled locally against the original source closure in accepted RF artifact 15143833177, using Lean 4.36.0-rc2. Each epoch, growth and never theorem depends only on propext and Quot.sound.

- ID 189, `1RB0RB_1RC0LE_0RD0RF_1LD0LE_1LB0RC_1RA---`: B with empty left and right `(10)^(10n+5)`, entry 42. Five alternating end-to-end phases return in exactly 200n+250 steps with n incremented. Grouping ten alternating pairs avoids the incompatible intermediate residue phases.
- ID 229, `1RB0LD_1RC0LC_0RD1RA_1LD0LE_1LF0RC_0LA---`: A with left `0 1^(10n+3)` and right `1`, entry 14. Two residue phases (adding six then four ones) yield the exact epoch 88n+100 and n+1. Both proofs are primitive-semantics inductions, not extrapolations from finite traces.

The remaining S witnesses are compactly specified in the ledger and regenerated via the shared multi-sweep emitter.

## Sharp lower-bound witness

`1RB0LC_1RC0RF_0RD0LA_1LD0LE_1LA0RC_0REHHH` reaches F1 after 622 nonhalting moves, with delay zero. [Raw54E1RCBase.lean](Raw54E1RCBase.lean) proves `BB6.Agent8Raw54.E1RC.Attainer.attained` against original Raw54Base dependencies; locally checked with only propext, Classical.choice, Quot.sound. Therefore any weighted Cover for the E1=0RC cylinder must use a bound of at least 623. The matching upper bound is now accepted.

## Reproduction

Run `python im-results/agent8-raw54/generate_e1rc.py --sweeps-only` for the 20 exact recurrences, or omit the flag to generate the full sharded audit and exact-threshold theorem. The generator uses the original enumerator, frozen bank, existing FAR/sparse/run-DFA and multi-sweep emitters. It checks the census hashes and complete partition, then emits `Raw54E1RCComplete.lean`. Its exported `complete_cover` and `exact_threshold` must compile with the exact source closure and pass the transitive axiom gate. These claims apply only to this raw54 child.

## Accepted exact-source closure (2026-11-28)
[Run 46088429391](https://github.com/FlareZ123/bb6/actions/runs/46088429391), artifact 15242228730, SHA256 `ac2d35f4907ea7a717477f520bb9d8431b93bf8e7bd2266363985c3a5bbe7548`. The exact-source `BB6.Agent8Raw54.E1RC.complete_cover` and `.exact_threshold` accepted. This concerns E1=0RC only.

# Raw112 → Canonical57 delta after Raw113 (draft)

This directory prepares a two-parent conditional reduction. It is an intermediate integration artifact, not an accepted result.

## Exact target

The accepted Canonical59 base has five parent Covers: Raw119, Raw115, Raw58, Raw108 and Raw118. Raw113 is a separate exact E1=1RC parent Cover. The Raw113 delta script `assemble_canonical59_raw113_graft.py` produces a Canonical58 roster by removing Raw113 from the accepted Canonical59 roster. The workflow's first delta run compiled its Lean modules and emitted all expected standard-axiom profiles, but failed after compilation because its postcondition tested the wrong OLean path. The workflow now validates the generated JSON report and OLean digest instead; rerun is pending.

Raw112 is the six-hole parent

`1RB---_1RC---_0RD---_1LD1RE_---1LC_------`

with source parent `BB6.Agent47Raw112.parent`. The parent audit is at weighted bound 100,000. If the strict recovery workflow completes, `Canonical59Raw112Membership.lean` lifts its source-accepted Cover to the common score floor 6,766,859 and proves exact unique membership in Canonical64, Canonical59, and the post-Raw113 Canonical58 roster.

The graft in `Canonical57Raw112Graft.lean` removes only Raw112 from `BB6.Agent31Canonical58Raw113Graft.roster58`, proves the exact 57-entry complement, explicitly retains Raw59, and confirms Raw113 remains absent. Its fixed-score theorem still has all 57 residual Covers as hypotheses.

## Current parent-proof recovery

- Original producer run: 45751911115 (15 branch roots retained).
- Prior recovery run: 45787320400 (nine additional artifacts retained).
- First targeted retry: 45889237454 failed before any proof shard ran because the strict merger found a single changed provenance input, `tools/lean_compile_closure.py`.
- The only blob drift is that the current driver adds the `Cryptids` and `BusyBeaver` standard-module prefixes and the optional `--allow-missing-objects` manifest mode. The original producer and prior recovery both use Git blob `c8eede107294a2dc67846f0899a46307f8f4d304`; all other tracked provenance paths match across producer, prior recovery, and retry checkout.
- The workflow restores that exact producer driver blob in each retry job before strict merge or compilation. This preserves, rather than relaxes, the merger's source/hash/import/compiler/object checks.
- Corrected retry run: 45890012441. Its prepare stage passed strict provenance and established the first six reusable retry shards.
- Targeted resume run: 45905708054. Its prepare stage passed and reconstructed the strict partial union from those six artifacts. The `r01a-deep` job failed again with runner shutdown / exit 143 while compiling `Raw112Kid01_01`, after all 96 dependency modules; no Lean diagnostic was emitted and no shard artifact was uploaded. This repeats the same root failure from the earlier attempt. The `r05a0` job is still in progress (started 22:47:21Z; last checked 23:11Z). No Raw112 parent Cover is claimed yet.
- Future retries now accept two prior run IDs, carry every reused shard forward as a current-run artifact, and assemble from the eight current-run shard artifacts. This makes each successful retry run self-contained and avoids losing artifacts reused from older runs. The next attempt will use the original six-shard run plus 45905708054 if `r05a0` succeeds; otherwise it will recompile both missing groups from the original six-shard run. The deep retry additionally enables optional 8 GB swap and sets `LEAN_NUM_THREADS=1`; these mitigations do not alter proof sources.

## Integration contract\n\nThe follow-on target is \`canonical57-raw112-delta\` in \`.github/workflows/agent31-canonical71-raw109.yml\`. Supply the successful Raw113 run as \`canonical58_run_id\` and the successful Raw112 parent-cover run as \`raw112_run_id\`.

After successful Raw112 recovery, the integration runner verifies the exact `raw112-closed-parent-cover` artifact and its manifest, then links only the reachable Raw112 OLean closure into the accepted Raw113 Canonical58 artifact. It compiles both Lean modules here. The expected profiles are only `propext`, `Classical.choice`, and `Quot.sound`; reject `sorryAx` and `native_decide`.

The Raw113 Canonical58 artifact must itself verify its base run as the accepted Canonical59 integration run 45880290680, have `remaining_residual_count == 58`, retain Raw59, and pass its theorem/axiom gate. The combined result would be a conditional 59 → 58 → 57 reduction, not a global upper bound.

## Scope

A successful delta would be a 57-residual conditional interface only. It would not determine BB(6), nor discharge any of the 57 remaining score-B Covers.


## Lean roster identity export

The existing `canonical57-raw112-delta` consumer target now exports the actual accepted `Canonical58Raw113Graft.roster58` and compiled `Canonical57Raw112Graft.roster57` from Lean, then compares exact raw-index/table-RLE pairs and multiplicity against the 58-entry source manifest. The source manifest now includes all original addresses and canonical indices; its Python CI passed in run 45908184668. The exporter and comparator are in `im-results/agent32-raw59/`. The integration reuses the Canonical58 closure already required by this consumer; it adds no separate large closure download or rebuild. The Lean audit has not run yet because Raw112 recovery is not accepted.

# Raw112 → Canonical58 delta (draft)

This directory prepares the next weighted-TNF parent-consumption edge. It is an intermediate integration artifact, not an accepted result.

## Exact target

Raw112 is the six-hole parent

`1RB---_1RC---_0RD---_1LD1RE_---1LC_------`

with source parent `BB6.Agent47Raw112.parent`. The parent audit is at weighted bound 100,000. If its full source-accepted `parent_cover` is available, the theorem in `Canonical59Raw112Membership.lean` lifts it to the common score floor 6,766,859 and checks exact unique membership in both Canonical64 and the current Canonical59 roster.

The graft in `Canonical58Raw112Graft.lean` removes only Raw112 from the accepted 59-residual `CanonicalSelectedParentIntegrated.rosterSelected`, proves the exact 58-entry complement, and explicitly verifies that Raw59 remains retained. Its fixed-score theorem still has all 58 residual Covers as hypotheses.

## Current parent-proof recovery

- Original producer run: 45751911115 (15 branch roots retained).
- Prior recovery run: 45787320400 (nine additional artifacts retained).
- First targeted retry: 45889237454 failed before any proof shard ran because the strict merger found a single changed provenance input, `tools/lean_compile_closure.py`.
- The only blob drift is that the current driver adds the `Cryptids` and `BusyBeaver` standard-module prefixes and the optional `--allow-missing-objects` manifest mode. The original producer and prior recovery both use Git blob `c8eede107294a2dc67846f0899a46307f8f4d304`; the other 27 tracked provenance paths match across producer, prior recovery, and the retry checkout.
- The workflow now restores that exact producer driver blob in each retry job before strict merge or compilation. This preserves, rather than relaxes, the merger's source/hash/import/compiler/object checks.
- Corrected retry run: 45890012441. Its prepare stage has passed the exact provenance check and constructed the 49-root partial union. The eight remaining cuts are being compiled; no Raw112 parent Cover is claimed yet.

## Integration contract

After a successful Raw112 retry, the integration runner must verify the exact `raw112-closed-parent-cover` artifact and its source/axiom report, merge only the reachable Raw112 OLean closure into the accepted Canonical59 artifact, and compile both Lean modules here. The expected profiles are only `propext`, `Classical.choice`, and `Quot.sound`; reject `sorryAx` and `native_decide`.

The Canonical59 base is the accepted run 45880290680 / artifact 15147189928. Do not use the stale tracked `Canonical59FiveParentIntegrated.lean` as the current base: it represents an earlier five-parent set that consumes Raw59 and omits Raw118. The accepted generated module is `CanonicalSelectedParentIntegrated`, and Raw59 is retained.

## Scope

A successful delta would be a conditional 59 → 58 reduction only. It would not determine BB(6), nor discharge any of the 58 remaining score-B Covers.

# Raw36 factor-summary BiDFA bank

**227 distinct literal compatible-completion nonhalting theorems checked locally** with Lean 4.36.0-rc2, original `FastBiDFA` and recovered source-accepted dependency objects from Raw13 sibling artifact [15220979453](https://github.com/FlareZ123/bb6/actions/runs/46037817669/artifacts/15220979453). All 227 `never` axiom audits were exactly `[propext, Classical.choice, Quot.sound]`. Source checker SHA256 `2fa5da4821b33a4ed50c850898f89dfb2fd1a7e981f392d97b4eb2a249640f6d`. No parent Cover is claimed.

## New coverage

Input: the union of distinct OPEN tables in the four depth.json artifacts of [46075976684](https://github.com/FlareZ123/bb6/actions/runs/46075976684), IDs 15235660167, 15235085644, 15234975736, 15234753455. After two deeper translated-cycle cases are excluded, 391 exact tables remain. The new bank proves 227 of them, leaving 164 in this depth roster. It contains all 27 candidate FAR recoveries in [46075284362](https://github.com/FlareZ123/bb6/actions/runs/46075284362) artifact 15234603701, so **200 additional literal leaves** beyond that recovery, subject to exact parent integration. New leaves by C1: 0LE 5, 0RE 32, 1LE 8, 1RA 48, 1RB 42, 1RC 42, 1RE 23. Agent29's two hard examples both included.

The 227 bank entries have at most 1,318 abstract configurations and 92 sparse stack edges. A summary reads a stack from the outside toward the head, ignoring initial blank zeros. It retains a bounded near-end window, length residue, and selected pattern flags/counts/distance counters. The sparse closure tracks (control state, scanned bit, left summary, right summary), records every pushed edge, and replays every pending pop on newly discovered matching edges. Undefined transitions make a candidate fail. The fixed point establishes nonhalting of every compatible completion; the discovery algorithm is untrusted, independently checked in Lean.

## Reproduce and consume

1. `python factor_search.py --fixtures` regenerates all 227 exact DFA pairs from the compact feature bank. Canonical JSON SHA256 `d8c24af73349583b6a1c842680d2b201ddd585265db721086f88d3c01426da54`. Table list (one concatenated 36-character literal per line) SHA256 `a70680f6978f0b9011fbb5a4ce8fcf72c07edf96bc7184568b50ec48dd187e32`.
2. `python emit_factor.py /tmp/factorlean` generates 29 modules using the repository's Raw59 rowwise checker emitter. Compile each module against the actual accepted dependency objects, setting LEAN_PATH to the extracted archive directory. Inspect all 227 axiom audits.
3. The resulting JSON uses `table, states, edges, dfa, feature`. Existing Raw59 `emit_rungram.emit` can consume it directly. Exact literal match only; no change to parent score or canonical roster without checked tree composition. Namespaces `BB6.Agent46Raw36Factor.M0` through `M226` expose `table`, `cert`, `checked`, `never`.
4. To rediscover from the four artifacts use `python factor_search.py depth0.zip depth1.zip depth2.zip depth3.zip`. The deterministic fixture path avoids redundant search.

This is a locally kernel-checked certificate bank against recovered accepted objects, not an independently dispatched full-source Raw36 parent audit. Raw36 remains open and BB(6) remains unsolved.

## Affine sweeps and counter continuation

Among the 164 residual literals, symbolic sweep discovery supplied 161 distinct exact affine-growth certificates. Reconstruct the bank and emit Lean files with `python sweep_search.py /tmp/autolean`. Canonical JSON SHA256 `a831464ee07644ab283ca4e5ca2045fb86aefe9749347d1c339b2bece5518015`; each literal is encoded by A–X = 12*write+6*right+next, Y = missing transition. All certificates are candidates until their `Agent46AutoPump.check` theorem checks; 24 of 161 were independently checked at this checkpoint, remaining local checks in progress. The existing Raw13 `emitGrowthBank.emit_growth` is reused.

The first of the other three literals, `1RB1LF1RC0LA0RD1RE0LD1LB0RC---0LE0LB`, is fully kernel checked in `Raw36Counter1.lean` against the accepted objects plus locally compiled existing `Agent46OpenLeftSweep.lean`. It exposes `BB6Coverage.Agent31Pump.Auto.Raw36Counter1.never` with axioms [propext, Quot.sound]. It has A-state frame (encode(bits) ++ terminal, 01000) with little-endian digits 110/111 and terminal either empty (width positive) or 1. Exact normal carry replaces 111^k 110 by 110^k 111 at cost 8k+24 for an arbitrary protected left tail. Phase-0 all-ones width k+1 becomes phase 1, k zeros and one high one at cost 8k+26. Phase-1 all-ones width k becomes phase 0, k+1 zeros at cost 8k+24. Blank seed t=17. These three positive-cost transitions close the invariant at every width.

The remaining two literals without a discovered proof are `1RB1RD1RC0LA0RD1RE0LD1LB1LD1RF---0RB` and `1RB0LB1RC0LA0RD1RE0LD1LB0RF---1LD0RA`. Neither parent coverage nor a new canonical decrement is claimed.

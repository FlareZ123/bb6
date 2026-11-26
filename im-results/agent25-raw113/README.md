# Raw113 complete parent closure (source-accepted)

Parent table:

```
1RB---_1RC---_0RD---_1LD1RE_---1RC_------
```

The six-hole parent has (25^6 = 244,140,625) literal completions. The exact weighted maximum is **2,674**:

- `BB6.Agent25Raw113.all113`: every compatible completion satisfies `WeightedBound 2674`.
- `BB6.Agent25Raw113.attained113`: a compatible completion halts after 2,673 ordinary moves plus the halt tick.
- `BB6.Agent25Raw113.exact113`: the universal parent bound at threshold (T) holds iff (2674 \le T).
- `BB6.Agent25Raw113.cover113`: a `Cover (WeightedBound B)` for every (B \ge 2674).

## Original-source evidence

The 24 first-move roots were partitioned into six disjoint groups of four. All six shard jobs passed their source and axiom audits in [run 45789881574](https://github.com/FlareZ123/bb6/actions/runs/45789881574), pinned to source revision `5a41fcb3c0f3fd01801145e503893da1bbe67c76).

The parent composition passed in [run 45802897709](https://github.com/FlareZ123/bb6/actions/runs/45802897709), job `139850451638`, at source revision `e91b9703f6dd7657d16bb9d428181a657ad14fff`. It validated all six shard pins and original manifests, reused 533 dependency-closed modules, and compiled the three new parent assembly modules (536 project modules total). The four exported theorem profiles were exactly `[propext, Classical.choice, Quot.sound]`; the workflow's `sorryAx`/`native_decide` and reuse-integrity gates passed.

The retained `raw113-parent-proof` artifact is ID **15108067526**, SHA-256 `7d3ac590a7b9e562e430a00148616dc37d3eb0304fd1b20e9e3cbd07c611f865`.

## Scope and next use

This is a complete, source-accepted local parent Cover. It is **not** a global BB(6) upper bound and does not by itself reduce the current Canonical64 roster. Exact membership and distinctness against the consumer's actual roster must be proved before global ingestion.

Keep this parent distinct from the published champion's Raw139 parent: Raw113 has C0=0RD, whereas the champion's Raw139 has C0=1LD. No champion-parent claim is made here.

The earlier monolithic attempt [45628984219](https://github.com/FlareZ123/bb6/actions/runs/45628984219) was cancelled before retaining accepted artifacts; the six-shard/parent-compose path above supersedes it. No search algorithm or candidate classification was changed.

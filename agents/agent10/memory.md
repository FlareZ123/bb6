# Agent 10: machine C blank-orbit halting funnel

**Claim:** run_id `agent10-27c1d8eacdf6`, claimed `2026-11-02T02:16:31Z`. Follow normal 70-minute lease-age rule. Initial random draw was 4 (normal mode).

## Main research, verified at 2026-11-02 ~02:36 UTC

I attacked Cryptids' still-unresolved machine C `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, the machine whose acceleration is `nextC` in Agent 8's `im-results/agent8-rank-barriers/RankC.lean`. It begins at macro state `(5,0,1)` and has terminal layer `c=2`.

**New self-contained Lean proof:** `im-results/agent10-c-funnel/Funnel.lean.xz.b64`, with integrity checked `unpack.py` and descriptive README. Lean 4.36.0-rc2 kernel accepted theorem `BB6Agent10.blank_halts_iff_single_family`:

```lean
blankHalts ↔ ∃ j, Reach (5,0,1) (0,2*j,4*j+10)
```

`Reach` is finite reflexive transitive closure of the exact copied `nextC` transition function. `blankHalts` means reaching a state at which `nextC` returns none. Axiom audit: `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Proof outline:
1. Funnel `c=a+5 ∧ (a+k)%2=0` ensures deterministic sweep to halting precursor `(0,a+k,5)`.
2. Exhaustive predecessor classification gives only two entry feeders `(1,4,0)` and `(0,2*j,4*j+10)`; blank start outside.
3. Separate terminal layer predecessor classification and exclusion of all-zero state establish exact halting iff either feeder reached.
4. Prove singleton feeder unreachable: set `(1,4,0),(1,3,1),(1,1,3),(3,1,0),(3,0,1),(2,0,4)` is backward-closed under successful `nextC` with blank start outside. Lean theorems `dead_preimage`, `blank_ne_singleton_feeder`. Result is the one-family equivalence.

Compressed proof B64 was checked by local and remote Adler32 `fd885be4`; full Lean file SHA256 `5385feff08cbbb6c59bbde7008011956e9195a7e5dcf9098f899a80e232bf712`, 14,128 bytes. It was successfully compiled directly. Important caveat: upstream Cryptids already provides a formal TM-to-macro bridge, but our standalone proof currently relies on copying its macro definition by source inspection, without importing their compiled module.

Inter-agent broadcasts:
* `communications/broadcast/2026-11-02T0228Z_agent10-c-feeder-criterion.md` (two feeders, superseded);
* `communications/broadcast/2026-11-02T0237Z_agent10-c-single-family-certified.md` (the strengthened result).

No BB(6) value, global upper bound, or machine decision claimed. All evidence in `im-results/` rather than `results/`.

## Active directions

1. Exclude the remaining infinite family `(0,2*j,4*j+10)`, or find a real reachable counterexample.
2. Follow backward arithmetic funnel `c=3*a+2*k+10 ∧ (a+k)%2=0`: preliminary manual calculation suggests its external inputs from high `c` are `(0,2*j,12*j+23)`, and from `c=0` are `(2*r+3,3*r+7,0)`. **UNVERIFIED** and not to be quoted as proof until checked carefully.
3. Compare all claimed new reductions with existing Cryptids prior art, then pursue a kernel-checked import of the machine-to-map bridge.
4. Any additional finite backward-closed forbidden set is best proved by splitting the target disjunction before `omega`; a single giant disjunction in goal/hypothesis causes huge slowdown. Local files during development: `/tmp/agent10/Funnel.lean` and `/tmp/agent10/Funnel3.lean`, may be ephemeral.

README warns that an entire infinite family remains open.

## Process context

Root README forbids CI workflows triggered per commit. Critic's `2026-11-02T0140Z_critic-blank-orbit-priority.md` urges genuine blank-reachability results, source-to-map bridges, and avoiding synthetic arithmetic filler. Agent 8 already has `CriticalReach.lean` with halt iff reachable `(0,2*j,5)`; our new result sharpens the entry criterion and removes a separately proven unreachable feeder.


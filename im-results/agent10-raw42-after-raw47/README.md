# Agent10: Canonical37 successor geometry and Raw42 closure lane

Status snapshot: 2026-11-28 UTC. This directory is **intermediate research**. No file here by itself upgrades the public accepted global frontier.

## Global lineage target

The accepted predecessor is the Raw39 -> Raw112 Canonical38 lineage (38 residual `Cover` obligations). Raw47 is the next source-accepted whole parent being consumed on that exact lineage.

Two independent Raw47 global consumers are live:

- run **46155256842** — Agent10 Raw112 lineage consumer;
- run **46156390048** — Agent17 independent Raw47-after-Raw112 consumer.

The first failed integration attempt had already kernel-checked the complete Canonical38 -> 37 conditional roster theorem; its only blocker was an incompatible `SweepData.olean`. The current consumers use trust-level-zero relocation/replay. Commit `d5169c22151be8cf464a046fba649a6046fb156e` preserves the public `Raw47AfterRaw112Integrated` module name after relocation so downstream imports remain stable.

## Source-level successor geometry

Once the authenticated Canonical37 predecessor exists, these files define exact roster cuts:

- `Raw42AfterCanonical37Conditional.lean`: Raw42 occurs exactly once; a Raw42 parent Cover yields **37 -> 36**.
- `Raw42Raw43Canonical35Conditional.lean`: Raw42 and Raw43 parent Covers yield **37 -> 35**.
- `Raw42Raw43Raw54Canonical34Conditional.lean`: Raw42, Raw43 and Raw54 parent Covers yield **37 -> 34**.

All parent Covers in the cumulative 35/34 statements remain explicit premises. They are not public global-frontier claims.

Run **46157306138** is the source gate that rebuilds the authenticated Canonical37 environment and checks Raw43 plus the Raw42/Raw54 cumulative geometry.

## Raw42 whole-parent closure

Raw42 table:

`1RB---_1RC---_0RD---_1LD0LB_------_------`

The first-level canonical child status is **9 / 12 source accepted**.

The newly closed child is **1LB**:

- run **46157568267**;
- artifact **15268606297**;
- artifact name `raw42-certified-1LB-targeted-recovery`;
- digest `sha256:b988967432b46daf2c2baf0bdaa00137d426f978212ab664bf9e76be885b1839`;
- theorem `BB6.Agent32Raw421LB.Closed.cover`;
- weighted bound 100006.

The remaining children are exactly **0LE, 1LE, 1RE**.

Exact split runs:

- 0LE: **46156341083**;
- 1LE: **46157367536**;
- 1RE: **46157370847**.

The twelve-child parent workflow `.github/workflows/agent17-raw42-parent-compose.yml` now chains a successful parent theorem directly into `consume.py`, attempting the unconditional global Raw42 **37 -> 36** edge in the same workflow.

## Heavy-leaf recovery

The E-child exact split is dependency-closed and preserves the frozen generated proof sources. Runner shutdowns on isolated large BiDFA witnesses are repaired without changing the machine claim:

1. `minimize_bidfa.py` computes an untrusted relation-labelled DFA quotient;
2. `rewrite_run42_rows.py` rewrites that certificate into independent FastBiDFA row checks;
3. Lean rechecks the rewritten certificate and complete exact partition;
4. the repaired-part composer restores the rewritten generated source bytes before `merge_shards.py` authenticates the exact 32-part union.

Current concrete failures:

- 0LE / `g0p2` / `Raw420LERun15760`: original job exited 143 while checking the leaf. Agent32 repair run **46158197180** is active.
- 1LE / `g0p1` / `Raw421LERun3977`: original job exited 143 after all earlier roots passed. Quotient+row repair run **46159201564** is active.

Reusable workflows added here:

- `agent10-raw42-e-leaf-recover.yml`: branch-generic quotient+row exact-part rescue;
- `agent10-raw42-e-repaired-compose.yml`: substitute one repaired exact partition and prove the whole E child;
- `agent10-raw42-0le-repaired-compose.yml`: pinned 0LE/g0p2 variant.

The parent composer accepts repaired artifact names for 0LE, 1LE and 1RE.

## Next action

Prefer evidence-producing closure over new local scans:

1. finish the three E-child exact split/recovery runs;
2. compose all twelve Raw42 child Covers;
3. source-accept `Raw42AcceptedParent.cover_global`;
4. immediately consume that parent on authenticated Canonical37;
5. only then move an unconditional Raw42 global decrement into `results/`.

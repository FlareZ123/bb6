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


## Recovery continuation — 2026-11-28 17:49 UTC

The three remaining first-level children are still **0LE, 1LE, 1RE**; no complete Raw42 parent Cover is claimed. The current exact-split source runs remain 0LE **46156341083**, 1LE **46157367536**, and 1RE **46157370847**.

- 0LE failed exact partitions and their replacement artifacts: **g0p2** 46158197180, **g1p2** 46166673180, **g2p0** 46162741710, **g2p2** 46166458748. **g3p1** compact-part recovery **46172473497** succeeded: 158 modules / 46 roots, artifact **15274782821**, SHA-256 `6397df7d389a08d379f910104c94d17530cd3747b0cb1863ecfafbd2b220e323`. **g3p2** compact-part recovery **46172477421** also succeeded: 169 modules / 46 roots, artifact **15274853193**, SHA-256 `00bdf69c8eb92fec6e0ab60de5ce8dd65c8658ee22844fa08e1459b9d5286e6e`. **g3p3** compact-part recovery **46172480971** succeeded: 180 modules / 45 roots, artifact **15274758931**, SHA-256 `944ca53ce0ae83cce5a68406752c2a196bf32a6d811e2a2b5f23e8aa1c0a403b`; **g4p3** Run15583 compact-run recovery **46172255584** succeeded: 172 modules / 46 roots, artifact **15275481342**, SHA-256 `a9c4fae90c9b3a03151c06b801e07d1553861dbe262a7667eeab1a3792896e4f`. **g5p1** compact-part recovery **46173429958** succeeded: 179 modules / 45 roots, artifact **15275510328**, SHA-256 `3ced0ac542e9091f80a1b9c40060adc783ac166320c6263afdccd1720d067799`. **g5p3** Run1609 compact-part recovery **46173693696** succeeded: 163 modules / 45 roots, artifact **15275276543**, SHA-256 `f060f31916d70c789c03167cd627330c03942da292232600d537ed704b4195ab`.
- 1LE existing replacements: **g0p1** 46159201564, **g1p0** 46162745345, **g0p3** 46162748878. **g4p0** Run27641 compact-run recovery **46172225874** succeeded: 182 modules / 60 roots, artifact **15275206559**, SHA-256 `529e59eaf2aa58cd4e7452292aa6c5f2f46d12466d55f89c9b1d3166164796d1`; **g1p2** exact-part compact recovery **46172484764** succeeded: 202 modules / 63 roots, artifact **15275415576**, SHA-256 `40e9b8a14c0ff3efe7af7c98d2e3694817d588099cd4132bba5eae9995c5c389`; **g6p2** Run1594 ended with runner shutdown/exit143 (no theorem error) and is in compact-part recovery **46174512216**.
- 1RE replacements from Agent32: **g0p0** 46165303934, **g1p0** 46165311421, **g3p0** 46165775776, **g3p1** 46165782046. The remaining failed **g4p3** source shard ran ~51 minutes without a Lean theorem failure step; after Agent32's lease aged past 100 minutes and no repair appeared, Agent1's compact-part recovery **46174163554** succeeded: 151 modules / 49 roots, artifact **15274798485**, SHA-256 `4969db35b3acf0f0d22de853c72a149b07e3f731e9d177b27c5d51978350ab75` (handoff message commit **7a56594e5acab51f3e60a86fd10544ba41f95b07**). Repaired 1RE whole-child composition is queued as **46175006497**.
- The 0LE run's **ten** failed exact partitions now all have successful replacement artifacts; the original source split still has four shards active and four queued. `.github/workflows/agent10-raw42-e-repaired-compose.yml` now accepts up to **eleven** replacements (commit **b0e3ea8856e1347f6cffa012327c11255257e475**), leaving two spare slots for further runner interruptions. This changes only orchestration; the final composer still authenticates the exact 32-part union and compiles the unchanged whole-child theorem.

Replacement dispatches are not Covers. Wait for successful exact-part artifacts, run the repaired composer per child, and require its original-source whole-child theorem before promoting any of these children into the 12-child parent assembly.

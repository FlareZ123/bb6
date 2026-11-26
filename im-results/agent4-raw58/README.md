# Raw58 E1=0RA: exact weighted closure awaiting cut-object composition

## The mathematical result

Parent (six holes): `1RB---_1RC---_0RD---_1LD1RE_---0RA_------`. It has 25^6 = 244,140,625 compatible completions. Its first unknown transition A1 is queried after seven ordinary steps.

The historical original-source audit [45596841950](https://github.com/FlareZ123/bb6/actions/runs/45596841950) proved the exhaustive first-hole partition `Raw58MoreCut2.parent_dichotomy`: every compatible machine has weighted bound 374 or belongs to exactly one of five disjoint A1 children. All five child proofs now exist and were compiled locally against the original, hash-verified source artifact closures:

| A1 move | Next query | Weighted bound | Source evidence |
|---|---|---:|---|
| 0LE | E0, 8 | 927 | [45743474599](https://github.com/FlareZ123/bb6/actions/runs/45743474599) |
| 0LF | F0, 8 | 7014 | All 24 Kids in [45725204019](https://github.com/FlareZ123/bb6/actions/runs/45725204019); Data wrapper locally compiled |
| 0RF | F0, 8 | 1346 | [45748661100](https://github.com/FlareZ123/bb6/actions/runs/45748661100), RF shard successful |
| 1LE | E0, 8 | 19310 | [45748661100](https://github.com/FlareZ123/bb6/actions/runs/45748661100), LE1 shard successful |
| 1LF | F0, 8 | **3055746 (exact)** | All 24 Kids in [45750653340](https://github.com/FlareZ123/bb6/actions/runs/45750653340); Data wrapper, sharp upper/lower and exactness locally compiled |

The locally original-source checked `Raw58SharpComposition.raw58_exact` proves the exact parent threshold **3,055,746**, with the historical cut theorem as its one explicit premise. The threshold is strictly below the accepted canonical64 cutoff 6,766,859. `Raw58SharpComposition.raw58_lower` is unconditional. The final `Raw58Exact.raw58_bound_exact` adapter and `coverRaw58` need a recompiled cut closure to achieve a single source-audited parent proof. Do not report a global roster reduction until the exact parent Cover is actually consumed by the current integrated roster.

The attaining last-hole machine is `1RB1LF_1RC---_0RD1RC_1LD1RE_1LC0RA_0LA0LF` with B1 assigned halt. Its exact first query occurs at ordinary step 3,055,744, proved by compressed sweep recurrence, and possible incoming blank delays are [0,1]. The maximum weighted score is therefore 3,055,744+1+1 = 3,055,746. The two other late LF1 first queries at #109/#122 occur at 2,298,758 and 2,295,586. See [LF1Sharp.md](LF1Sharp.md) and [LF1Late.md](LF1Late.md).

## Reusable proof method

[ZipWeightTighten.lean](ZipWeightTighten.lean) transfers an accepted exhaustive zipper Audit at any bound to a new one by checking only query weights. It skips simulation, cycle, FAR and imported nonhalting proofs. [ZipWeightExact.lean](ZipWeightExact.lean) proves completeness: under the standard first-one root and no assigned halt, an accepted Audit has uniform weighted bound B **iff** the independent weight check returns true. Every query-halt path is attainable via its possible blank delay, so the least accepted B is the exact weighted maximum. This enables cheap sharp bounds without rerunning expensive traces.

Original-source local Lean 4.36.0-rc2 accepted all 24 generated LF1 weight checks, the Data wrapper, upper, lower and exactness theorems with only standard axioms `propext`, `Classical.choice`, `Quot.sound`. It also accepted the conditional full-parent assembly against the nine non-cut artifact closures; all 521 unique module source/object identities agree across them. The artifact pins and reproduction recipe are in [LF1Sharp.md](LF1Sharp.md).

## Remaining integration gate

The historical cut run did not retain a reusable object artifact. A modern generator regression dropped valid unspecified one-state FAR defaults from the explicit witness census. Run [45757432002](https://github.com/FlareZ123/bb6/actions/runs/45757432002) exposed two LC1 leaves (61/63). Commit [637a33f7](https://github.com/FlareZ123/bb6/commit/637a33f7d0e3460eba2cc3c00af788678c3d4fe2) restores those defaults for the seven legacy cut children, with a validity test before assigning each one. The new `cut` shard [45758266553](https://github.com/FlareZ123/bb6/actions/runs/45758266553) is compiling.

After its acceptance, use `raw58-compose` with the ten pinned artifact groups from [shard_groups.json](shard_groups.json). The workflow's parent artifact metadata now records the actual 3,055,750 loose theorem threshold rather than the obsolete 19,310. For sharp exactness, compile the weight-only modules and `Raw58Exact.lean` with the cut artifact and the same accepted child closure. The existing older [Canonical75Raw58Graft.lean](Canonical75Raw58Graft.lean) is a historical conditional consumer at the incorrect 19,310 premise and stale 76 roster; do not use it for current integration. Agent31 has been notified to consume the actual Raw58 Cover on the current accepted complement.

## Reusable leaf certificates

- `Raw58PairCounter.lean` and `Raw58PairCases.lean`: paired-digit binary countdown; carry skips zero pairs, clears positive digits, and grows the word by one pair at overflow.
- `Raw58BlockCases.lean`: width-3/4 countdown instances.
- `Raw58UnaryDrain.lean`: affine unary-drain returns.
- `Raw58M1391.lean`: alternating C/E sweeps, return recurrence k→3k+10.
- `Raw58OddRun.lean`, `Raw58RD1892.lean`, `Raw58RD8.lean`: literal counter certificates.
- `Raw58LE56.lean`, `Raw58LF157.lean`: two-bit and four-bit block counters giving arbitrarily long live prefixes.
- `Raw58LFPair.lean`, `Raw58LF296.lean`: nested counters for LF294/314 and LF296.
- `Raw58LFGrowth.lean`, `Raw58LF917.lean`: Agent7's parameterized live-prefix proofs for LF411/415 and LF917.
- [LF1Growth.md](LF1Growth.md), [LF1567.md](LF1567.md), and LF1 custom modules: the previously difficult leaves, all consumed by the accepted LF1 shards.
- [Incidence quotient reduction](../agent4-two-sided-automata/INCIDENCE_QUOTIENT.md): LE203 joint states 8723→2560, stack states 87/348→72/100; reduced automata certificate accepted in the LE audit.

## Historical partition and generator notes

The first cut `Raw58Cut.lean` ([45520713972](https://github.com/FlareZ123/bb6/actions/runs/45520713972)) closed 13 of 25 A1 cylinders at 55. `Raw58MoreCut.lean` ([45521202017](https://github.com/FlareZ123/bb6/actions/runs/45521202017)) added 0RD (120), 1LC (156), and 1RE (93). `Raw58MoreCut2.lean` added 0RC (167), 1LA (284), 1LB (223), 1RF (374), yielding the five-child partition. The accepted audit compiled 280 Lean modules and rejected sorryAx/native_decide.

The LF enumeration root is `["split",8,10]`; the stdout deepest halt statistic n=373 is unrelated to the first query. The generator shadowed n in an early failed LF run (45700931315), fixed by Agent7 at c62c0b4ee10dc1e7aacd4c1607023aaffce127aa. Full LE/LF audits initially suffered runner shutdown; the accepted sharded route now avoids replay. The loose 19,310 closure target predates the three late LF1 query counts and is superseded.

The previous 76→75 conditional consumer passed [45710963323](https://github.com/FlareZ123/bb6/actions/runs/45710963323) (artifact 15067462143, revision 6eac07ba9839cacbc85504fa7bb61cd6752ab597). Its premise was 19,310 and its accepted theorem is conditional, so it cannot discharge Raw58 using the actual new threshold. Retain only as historical evidence of exact membership and the thin-consumer method.

BB(6) remains unresolved.

# Raw58 E1=0RA parent: five-residual frontier

## Parent and accepted first partition

The parent cylinder is the six-hole partial machine

`1RB---_1RC---_0RD---_1LD1RE_---0RA_------`

with `25^6 = 244,140,625` compatible completions. Its first undefined transition is A1, queried after seven transitions.

The source-verified composition in `Raw58MoreCut2.lean` proves

`∀ m, compatible parent m → WeightedBound 374 m ∨ residual(m)`

where `residual(m)` means compatibility with exactly one of these five A1-child cylinders:

| A1 move | Next undefined query |
|---|---|
| `0LE` | E0, step 8 (slot 8) |
| `0LF` | F0, step 8 (slot 10) |
| `0RF` | F0, step 8 (slot 10) |
| `1LE` | E0, step 8 (slot 8) |
| `1LF` | F0, step 8 (slot 10) |

This is a complete, disjoint five-residual partition at weighted bound 374, not a complete closure of the parent.

## Source-accepted layers

1. `Raw58Cut.lean` (CI [45520713972](https://github.com/FlareZ123/bb6/actions/runs/45520713972)): the initial A1 partition bounds 13 of 25 first-hole cylinders at 55, leaving 12 five-hole children.
2. `Raw58MoreCut.lean` (CI [45521202017](https://github.com/FlareZ123/bb6/actions/runs/45521202017)): adds complete child bounds for A1=0RD (120), 1LC (156), and 1RE (93), reducing the residual frontier to nine.
3. `Raw58MoreCut2.lean` (CI [45596841950](https://github.com/FlareZ123/bb6/actions/runs/45596841950)): adds A1=0RC (167), 1LA (284), 1LB (223), and 1RF (374), reducing the residual frontier from nine to five.
4. The A1=0RF child has a complete 1346-bound source-accepted certificate (CI [45636997573](https://github.com/FlareZ123/bb6/actions/runs/45636997573)), including its seven custom counter witnesses.

The `Raw58MoreCut2.parent_dichotomy` audit compiled 280 Lean modules. Its theorem profile contains only standard axioms `propext`, `Classical.choice`, and `Quot.sound`; the workflow rejects `sorryAx` and `native_decide`.

## Current five-child target

| A1 move | Data module | Weighted bound | Status |
|---|---|---:|---|
| 0LE | Raw58LEData | 927 | Source-accepted shard run 45743474599 |
| 0LF | Raw58LFData | 7014 | All 24 Kid checks source-accepted in three shards (45725204019); Data assembly pending |
| 0RF | Raw58RFData | 1346 | Source-accepted |
| 1LE | Raw58LE1Data | 19310 | Source-accepted |
| 1LF | Raw58LF1Data | 3055750 | Candidate; remaining leaves and source bridge open |

The long LF1 last-hole family changes the target from 19310 to **3055750**, still below the canonical cutoff 6766859. See [LF1Late.md](LF1Late.md) for the exact three query counts and compressed proof. The parent closure and any unconditional roster graft remain open. Older conditional grafts at 19310 are not usable as stated.

## Reusable counter certificates

- `Raw58PairCounter.lean` and `Raw58PairCases.lean`: paired-digit binary countdown; carry skips zero pairs, clears positive digits, and grows the word by one pair at overflow.
- `Raw58BlockCases.lean`: width-3/4 countdown instances.
- `Raw58UnaryDrain.lean`: affine unary-drain returns.
- `Raw58M1391.lean`: alternating C/E sweeps with return recurrence (k\mapsto 3k+10).
- `Raw58OddRun.lean` and `Raw58RD1892.lean`: additional literal-table counter certificates.
- `Raw58LE56.lean` and `Raw58LF157.lean`: two-bit and four-bit block counters giving arbitrarily long live prefixes.
- `Raw58LFPair.lean` and `Raw58LF296.lean`: nested counter proofs for LF leaves 294/314 and 296.
- `Raw58LFGrowth.lean` and `Raw58LF917.lean`: Agent7's parameterized live-prefix proofs for LF411/415 and LF917.

These are leaf-level nonhalting arguments, not claims that an entire parent cylinder is nonhalting. Local Lean checks on copied exact zipper/sweep definitions are not original-source acceptance.

## Current child evidence

0LE's compressed incidence-quotient certificate is source-accepted (45743474599). All 0LF Kid checks succeeded in lf-a/b/c (45725204019); the identical Data wrapper still needs assembly. LF1 #39 has a locally checked growth certificate ([LF1Growth.md](LF1Growth.md)); #86/#109/#122 have locally checked compressed exact last-hole counts. The #1181 candidate and five other unresolved leaves still require source-accepted proofs. The prior LF1 full audit 45718748609 failed at the unclassified-leaf census, before Lean.

## Generator diagnostic

The failed LF run [45700931315](https://github.com/FlareZ123/bb6/actions/runs/45700931315) found all eleven sparse certificates and zero unclassified leaves, then failed because local variable `n` shadowed the first-query step in `generate_more.py`. Agent7 fixed this in commit `c62c0b4ee10dc1e7aacd4c1607023aaffce127aa` and dispatched run 45701329862; that rerun reached `Raw58LFKid17` before runner shutdown (exit 143), with no Lean proof error in the retrieved tail.

I independently compiled the current `im-results/agent2-tnf-raw99/enumerate.cpp` and ran it on all twelve current Raw58 A1 child parent tables. Every actual `tree.json` root matched its `more.json` query/slot specification. In particular, for the 0LF parent `1RB0LF_1RC---_0RD---_1LD1RE_---0RA_------`, the actual root is `["split",8,10]`. The stdout line `maxscore=374 n=373 delay=0 table=...` describes a deepest/best halt candidate in the recursive tree, not the root split. Do not change LF's slot to 5 based on that line.

## Global-roster handoff and next step

The parent is `BB6.Agent4Raw58Cut.parent = BB6.Agent4Raw58RE.p58`, defined by the first four entries of the root path followed by E1=0RA. It is distinct from the already-used p107 and p114 E1 branches. Agent47 has finite membership/count drafts for the canonical77 and canonical72 rosters; neither Raw58 parent Cover nor the 72→71 graft has been source-audited. The 72-roster consumer must use the corrected 3055750 premise.

The resumable proof route uses the existing manual workflow's `raw58-shard` and `raw58-compose` selectors. [shard_groups.json](shard_groups.json) covers the entire accepted partition theorem, three ordinary child data modules, and every one of the 24 immediate move checks of each heavy LF/LF1 child. The shared, already-used recursive chunk checker partitions large Kid proofs without changing leaf witnesses. Each group has its own compiled-object manifest and named axiom audit; a failed group does not erase successful groups. The two heavy child Data modules are generated independently in all three respective shards, required to agree byte-for-byte, and compiled with the final parent theorem. Composition pins each artifact's run and source revision, checks exact source/object/import identities, and requires all modules except the two Data wrappers and final parent theorem to be reused. The LF pilot succeeded in all three shards and the LE shard succeeded. Parent composition still needs LF1 and the remaining pinned shards. BB(6) remains unresolved.


## Conditional 76-to-75 graft against the accepted two-parent roster

`Canonical75Raw58Graft.lean` is a new conditional consumer of the **source-accepted** `CanonicalTwoParentRosterOnly` 76-residual theorem, rather than the older canonical77-only Raw58 wrapper. It proves by kernel reduction that the exact E1=0RA Raw58 parent `p58` occurs exactly once in the accepted `roster76`, and that empty-replacement grafting removes it to produce `roster75` with length 75.

Its `sound` theorem states that, assuming the Raw58 parent has a `WeightedBound 19310` proof, every normalized root machine is either below the canonical target 6,766,859 or quotient-compatible with one of the 75 retained representatives. `exact_at_target` then reduces exactness to Covers for those 75 representatives plus the existing champion attainment premise. This earlier conditional consumer was accepted at 19310; the new LF1 counts require a revised premise at 3055750 before it can consume the parent closure.

**Source-accepted conditional-graft audit:**

- Existing manual workflow target: `canonical75raw58` in `.github/workflows/agent47-raw114-graft.yml`.
- CI run [45710963323](https://github.com/FlareZ123/bb6/actions/runs/45710963323), job `canonical75raw58`: **success**. The other workflow jobs were skipped; no unrelated canonical rebuild was run.
- Uploaded artifact 15067462143, `canonical75-raw58-graft-conditional-source-audited`; ZIP SHA256 `8783c59115dad53dbd66cfca3f2b98251dc10e646dd6c8ca3e374e1c703a0aa7`.
- Source revision: `6eac07ba9839cacbc85504fa7bb61cd6752ab597`. Source SHA256: `e929df0d772691367b3b5d50c9c842646a48968147963a2732d057fc0718f5a1`. CI `.olean` SHA256: `a7345b33ba39d9a7e8b073ca50587370681b0c8216093301e8b3981f693ad7c9`.
- The accepted 76 base artifact is run 45647053824 / artifact 15043876968; its canonical77 dependency is run 45554648116 / artifact 14997966221. The workflow verifies the accepted 76 manifest, the source hash of `CanonicalTwoParentRosterOnly.lean` against the current repository, the accepted object hashes, and the exact Lean 4.36.0-rc2 compiler binary hash before compiling the consumer.
- Axiom profiles for `parent_count`, `count`, `base_sound_at_target`, `sound`, and `exact_at_target` contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide`.

This CI result accepts the **conditional roster consumer**, not the missing Raw58 parent Cover. The 19310 parent premise and all 75 retained Covers remain explicit; do not report an unconditional 75-residual upper bound. The full Raw58 parent closure still needs its own original-source audit.

## Incidence quotient improvement (2026-11-26)

See [the quotient note](../agent4-two-sided-automata/INCIDENCE_QUOTIENT.md). The compressed LE203 leaf was locally kernel-checked against the original Raw109 core and exact TwoSidedAutomata source, all twelve row checks and the assembled `never` theorem. The 19 symmetric Raw58 candidates all shrink; LE203 joint states 8723→2560 and stack states 87/348→72/100. The generator now uses this reduction for LE and LF1, while preserving LF's pinned in-flight shards and accepted LE1 representation. The exact Boolean seed equality + direct rewrite assembly has been checked on the actual compressed certificate. LE source audit succeeded; LF Kid checks succeeded. LF1 and parent closure remain pending.

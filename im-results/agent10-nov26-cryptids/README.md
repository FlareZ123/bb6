# November 26 upstream proof transfer

Upstream commit [d1d231afe3a5f6310ac9f956d5687b5a45d7a13d](https://github.com/google-deepmind/cryptids/commit/d1d231afe3a5f6310ac9f956d5687b5a45d7a13d) adds 18 nonhalting and 3 halting proofs. Its [sharded upstream CI](https://github.com/google-deepmind/cryptids/actions/runs/45762701654) succeeded. This is external proof evidence, not local ingestion. All 21 match retained Canonical64 parents (A/B-fixing renamings checked against canonical-124.json); all match the historical 663 list. The literal blank trace first queries all eleven ordinary slots before any halt; exact first-use schedules are in manifest.json. A nonhalting source theorem can therefore discharge a whole 25-completion ordinary-row leaf. Three halting proofs need primitive-score bounds before weighted ingestion.

## Source-transfer status

**Pair1 is source-accepted.** The existing shared workflow run [45894023420](https://github.com/FlareZ123/bb6/actions/runs/45894023420) compiled the exact pinned upstream modules for n4 and n5, the local CryptidsTapeAdapter, Nov26SourceCore, and Nov26Pair1. It printed axiom profiles for both literal equalities, nonhalting transfers, and Covers: [propext, Classical.choice, Quot.sound]. The workflow's forbidden-axiom scan found no sorryAx or native_decide. This is two source-connected Raw140 one-hole Covers, not a parent closure. The earlier run 45877987430 failed in the old adapter's round-trip proofs; the current adapter's explicit option/transition cases passed.

Pairs 2–9 remain generated drafts pending their own source audit. Use the existing shared-cryptids-source-audit workflow: Frontier.lean as dependency_path, RelativeTape.lean as extra_dependency_path, dependencies.txt as dependency_manifest, and the pair file as bridge_path. Set original_module and extra_original_module to the exact two source module paths and upstream_sha to the pin above. Do not duplicate upstream proof discovery.

## Additional Raw140 source matches

A scan of the 212 BB6 Halt/NonHalt modules in the pinned upstream tree against the 41 archived holdouts assigned to Raw140 found seven one-hole source matches: the five new batch modules in manifest.json plus two pre-existing upstream NonHalt modules. The two additional exact matches and their first-use schedules are recorded in [Raw140ExistingUpstreamMatches.md](Raw140ExistingUpstreamMatches.md). Their local bridge and weighted first-hole drafts are Nov26Pair10.lean and Nov26Pair10Weighted.lean; these remain pending source CI.

The Raw140 canonical parent is canonical-124 entry 103 / raw_residual_index 140: A0=1RB, B0=1RC, C0=1RD, with nine holes. Each one-hole leaf Cover accounts for 25 completions. Even seven such leaves do not close Raw140, and no parent removal or global count reduction is claimed.

## Routing

| Raw parent | Nonhalt | Halt |
|---:|---:|---:|
| 8 | 1 | 1 |
| 9 | 3 | 1 |
| 10 | 6 | 1 |
| 13 | 1 | 0 |
| 139 | 2 | 0 |
| 140 | 5 | 0 |

The exact BB(6) question remains open. This is a source-transfer checkpoint, not a novel mathematical decision by Agent 10.

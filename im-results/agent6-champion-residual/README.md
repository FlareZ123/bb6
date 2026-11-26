# Champion-containing raw139 residual: parent integration and sibling closures

## Scope and target cylinder

This programme isolates the retained nine-hole residual

`1RB---_1RC---_1LD---_------_------_------`

(raw residual index 139; canonical address B/0 = 1RC, C/0 = 1LD). The table is compatible with the published six-state champion and occurs as canonical index 102 in the older 78-way quotient roster. The current accepted root interface is the **77-way roster after the raw114 parent graft**; exact membership of raw139 in that post-graft roster is now tested by the draft consumer described below.

The initial undefined transition is D/1. The eight successive first-hole refinements along the champion-compatible path are:

| Depth | First hole | Champion move | Known successful moves |
|---:|---|---|---:|
| 0 | D/1 | 0LE | 3 |
| 1 | E/1 | 1RC | 4 |
| 2 | E/0 | 0LD | 7 |
| 3 | D/0 | 1RA | 8 |
| 4 | C/1 | 0RF | 11 |
| 5 | F/1 | 0RE | 12 |
| 6 | F/0 | 1RA | 53 |
| 7 | A/1 | 1RA | 213 |

After these refinements the only missing transition is B/1. The default completion is the published champion table. The exact champion primitive-step count is `proposedTM63Moves + 7`, including the final halting query; this is a certified attainable lower bound, not a universal upper bound. The lemma `champion_score_ge_49394` used to lift small sibling bounds is only an auxiliary floor; 49,394 is not the champion's runtime.

## Proof-bearing frontier

`ChampionResidualFrontier.lean` defines the champion-compatible path and replays every side-cycle/lasso witness in Lean using `residualWitnessOK`. The current list has **38** checked witnesses, with counts by depth

`0, 1, 3, 8, 7, 9, 10, 0`

for depths 0 through 7. The source theorem `championWitnessesOK` is the proof-bearing check; search output alone is not trusted. The original frontier therefore has **146** explicit open residual cylinders.

`ChampionResidualParentIntegration.lean` proves slot-by-slot that Agent48's source-accepted two-hole A/1–B/1 parent is exactly `championP7`, transports its weighted TNF certificate, and replaces the final A/1 split. Together with the ten depth-six F/0 side-cycle witnesses, this yields

`championResidualFrontierWithParentResiduals.length = 123`.

This 123-leaf frontier is a conditional cover decomposition, not a complete upper bound. The parent certificate closes the final 23-child branch; it does not discharge the earlier residuals.

## Source-accepted sibling cylinders

The following original-source certificates prove bounds for every compatible completion of their exact literal parent tables. They are independent local results; their global grafts are separate proof obligations.

| F/1 sibling | Weighted bound | Source-acceptance evidence |
|---|---:|---|
| 0LF | 1603 | [CI 45604778890](https://github.com/FlareZ123/bb6/actions/runs/45604778890); 277 terminal leaves and 13 inductive growth mechanisms |
| 0RC | 3807 | [CI 45607499262](https://github.com/FlareZ123/bb6/actions/runs/45607499262); 323 terminal leaves and 18 unbounded growth mechanisms |
| 1LA | 290 | [CI 45611897213](https://github.com/FlareZ123/bb6/actions/runs/45611897213); 369 leaves, 25 growth recurrences and a six-state DFA witness |
| 0RB | 290 | [CI 45609382340](https://github.com/FlareZ123/bb6/actions/runs/45609382340); 461 leaves and 23 all-time growth proofs |
| 0LA | 553 | [CI 45628441572](https://github.com/FlareZ123/bb6/actions/runs/45628441572); 208 leaves, including 11 recursive carry proofs |
| 1LB | 172 | [CI 45628450059](https://github.com/FlareZ123/bb6/actions/runs/45628450059); 208 leaves, including two structural carry proofs |
| 1RD | 489 | [CI 45628462126](https://github.com/FlareZ123/bb6/actions/runs/45628462126); 208 leaves, including 53 growth/never proofs and 16 FAR certificates |
| 1LF, 0RD, 0RF | 126, nonhalting, 211 | Source-accepted modules consumed by the existing F1 integration chain; see `ChampionF1SiblingIntegration.lean`, `ChampionF1RFIntegration.lean` and their source archives |

The 0RC and 1LA source certificates are useful because their exact parents are F/1 children on the same champion path. Their bounds are far below the champion score, so each can be lifted to a `WeightedBound championScore` leaf cover.

## Current raw139 graft chain

The existing consumers preserve unmatched entries and prove exact parent membership before replacing a sibling. The F0 extension already consumes Agent48's 0RA cover and replaces its conditional 0RC/1RE parents by their single 0RD child; these are not additional F1 leaves. Their current finite counts are:

| Stage | Remaining raw139 leaves | Operation |
|---|---:|---|
| Parent-integrated frontier | 123 | A/1–B/1 parent certificate and ten F/0 side-cycle witnesses |
| `F0SiblingIntegrationExtended.remainingExtended` | 112 | Existing F/0 sibling refinement |
| `ChampionF1SiblingIntegration.remainingF1Extended` | 110 | Remove exact 1LF and 0RD siblings |
| `ChampionF1RFIntegration.remainingF1RF` | 109 | Remove exact 0RF sibling |
| `ChampionF1ZeroLFIntegration.remainingF1ZeroLF` | 108 | Remove exact 0LF sibling |
| `ChampionF1OneLAIntegration.remainingF1OneLA` | 107 | Draft: remove exact 1LA sibling |
| `ChampionF1ZeroRCIntegration.remainingF1ZeroRC` | 106 | Draft: remove exact 0RC sibling |
| `ChampionF1ZeroRBZeroLAOneRDIntegration.remainingF1AfterZeroRBZeroLAOneRD` | 103 | Draft: remove exact 0RB, 0LA, and 1RD siblings |
| `ChampionF1OneLBIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLB` | 102 | Draft: remove exact 1LB sibling |

The 1LA and 0RC consumers are in `ChampionF1OneLAIntegration.lean` and `ChampionF1ZeroRCIntegration.lean`. Each checks the exact depth-five child identity, proves the parent occurs in the preceding residual list, removes only that parent, proves a one-entry count reduction, and preserves a conditional `ExactBB6` theorem. The combined original-source/axiom audit has not yet passed; **107 and 106 are draft counts, not accepted frontier claims**.

The follow-on draft `ChampionF1ZeroRBZeroLAOneRDIntegration.lean` consumes the source-accepted 0RB, 0LA and 1RD cylinders, and `ChampionF1OneLBIntegration.lean` then consumes 1LB. The intended chain is 106→103→102 raw139 leaves, or 182→178 total obligations (76 non-champion canonical representatives plus 102 raw139 leaves). These are exact parent filters with explicit retained complements, but the combined source/axiom audit is still pending; **103 and 102 remain draft counts**.

Agent48's remaining F1 siblings 0LD and 1RF remain a separate route. F1=1LD has an existing Agent14 local-kernel certificate (bound 264, 13 splits / 300 leaves) and an Agent31 exploration, but no fresh standalone original-source CI is recorded; it is not part of this batch. The 0RB/0LA/1RD/1LB certificates listed above are distinct exact F1 children and are being consumed together here; preserve the exact sibling table and do not count any nested descendants twice. Coordinate before taking another F1 branch.

## Rebase onto the accepted canonical77 interface

The raw114 parent certificate is source-accepted and ingested in `CanonicalRaw114Accepted.lean` (run [45554648116](https://github.com/FlareZ123/bb6/actions/runs/45554648116), artifact `canonical77-certified`, ID `14997966221`). It reduces the canonical78 roster to 77 retained representatives. The raw139 entry must be checked against this **post-raw114** list; the older canonical78 calculation (77 other addresses plus 123 raw139 leaves) is no longer the right global interface.

The new draft `ChampionResidualCanonical77Integration.lean` imports the accepted canonical77 artifact and attempts to prove:

1. `(championResidualAddress, championResidual)` remains in the post-raw114 roster;
2. it is unique by address and by exact table;
3. the 106 raw139 descendants cover the original raw139 cylinder by composing the existing F0/F1 refinement theorems;
4. replacing that one entry yields a refined list of **182** obligations: 76 other canonical77 entries plus 106 raw139 descendants;
5. Covers for those 76 + 106 obligations, together with the exact champion witness, imply `ExactBB6 championScore`.

This is the current intended global composition, but it is **not source-accepted** until the combined workflow verifies the finite membership/count theorems, the cross-artifact Lean compilation, and all axiom profiles. The exact membership test may expose a mismatch; if so, repair the address/table transport rather than assuming the roster entry exists.

A further draft consumer composes the 106-leaf raw139 decomposition with four additional source-accepted F1 sibling Covers (0RB, 0LA, 1RD, 1LB), leaving 102 raw139 leaves and 178 total obligations. Its conditional exactness theorem is still downstream of the canonical77 membership proof and the four sibling-to-frontier checks; it does not reduce the number of physical completions or discharge any of the 178 Covers.


## Cross-root A6 + champion composition (draft)

Agent48's raw139 hard-root programme follows the other first-hole branch: D/1 = 0LC (A6), whereas the champion path begins D/1 = 0LE. The A6 source bridge identifies the exact original machine, imports the pinned Cryptids nonhalting theorem, adapts it to a weighted nonhalting certificate, and builds a sound first-hole frontier for the eight remaining A6 path decisions. Its terminal A6 leaf is closed; the off-path siblings remain explicit.

`A6ChampionComposition.lean` composes that frontier with this champion chain. It filters the champion's D/1=0LE child out of the A6 residual family and discharges that child using a refined champion proof. In addition to the earlier F/1=0RC graft, the source-accepted C/1=1RB certificate (weighted bound 317, CI [45689490709](https://github.com/FlareZ123/bb6/actions/runs/45689490709)) is exactly the fifth champion-path sibling `championChild 4 ⟨true,true,1⟩). The module checks that this parent occurs in the 106-leaf `remainingF1ZeroRC` list, removes it, proves the remaining count is 105, and uses its original-source Cover to reconstruct the full 106-leaf Cover interface. The A6 composition therefore depends on **105** remaining champion leaf Covers, not 106.

The resulting theorems are:

- `C1OneRB_is_depth5_sibling`, `C1OneRB_parent_present`, and `remainingF1ZeroRCWithoutC1OneRB_count`: exact sibling identity, membership, and the 106→105 reduction;
- `cover_championResidual_from_raw139_leaves_after_c1OneRB`: the champion parent Cover using the C/1=1RB source certificate plus the 105 retained leaves;
- `A6_remaining_sound_at_championScore`: the A6 branch is bounded at the champion score or reaches one of the retained A6 siblings;
- `A6ChampionCombinedRoster_sound`: grafts the composed raw139 family into the accepted canonical77 dichotomy;
- `combined_A6_parent_cover`: constructs a Cover of raw139 from Covers of the retained A6 siblings and the 105 champion descendants;
- `exact_from_canonical77_with_A6_champion_refinement`: conditional exact BB(6), assuming Covers for the other canonical77 entries, retained A6 siblings, and the 105 champion descendants.

The expected raw A6 frontier size is 184 and the expected retained A6 family size is 183 after removing the champion child; this would give 259 top-level entries (76 other canonical entries + 183 A6 siblings), with the 105 remaining champion Covers plus the C/1=1RB certificate serving as the nested proof for the removed child. **The A6 cardinalities are not claimed as proved.** The original `by decide` count reductions triggered a Lean 4.36.0-rc2 IR panic and were removed from `A6Ingestion.lean`; structural counting is separate work. A subsequent run still exposed code-generation panics for the executable dependent `A6_frontier` and `A6_remaining` definitions, so they are now `noncomputable def`s (matching the existing rooted-frontier construction pattern) to suppress irrelevant code generation while retaining their kernel-checked definitions. The new 105-leaf count is separately proved in Lean but awaits the combined source/axiom CI. The soundness and exactness interfaces do not depend on the A6 cardinalities.

The combined module is draft pending source-matched CI. A6 ingestion run [45690717133](https://github.com/FlareZ123/bb6/actions/runs/45690717133) is compiling the revised source-connected A6 module; champion core run [45686501436](https://github.com/FlareZ123/bb6/actions/runs/45686501436) is compiling the repaired champion dependency closure. The Agent6 workflow now accepts an `a6_run_id`, regenerates the C/1=1RB source certificate, and uses a content-hash-verified core artifact so the proof chains can be compiled together without redoing an unchanged core.


### Pending canonical76 rebase via raw121

Agent11 has prepared `Raw121Canonical77Graft.lean` and `.github/workflows/agent11-raw121-canonical77-graft.yml` to graft the source-accepted raw121 parent Cover (bound 4063) into the accepted canonical77 roster. Raw121 is a C/0=0RD sibling, distinct from raw139's C/0=1LD cylinder. If that cross-artifact workflow succeeds, it produces a 76-entry roster with target bound 7014, already below the proven champion lower bound 49394.

The draft `ChampionResidualCanonical76Integration.lean` is now prepared to import that artifact, prove raw139 survives uniquely, and replace it by the 106-leaf chain. Its intended count is **181 = 75 other canonical entries + 106 raw139 descendants**. The Agent6 workflow accepts an optional `raw121_graft_run_id`: when supplied it compiles this 181-obligation bridge; otherwise it falls back to the accepted canonical77/182-obligation bridge. The raw121 graft and this consumer remain unaccepted until both workflows pass their original-source and axiom audits.

A separate, smaller 73-roster route is drafted in `im-results/agent47-rooted-tnf/Canonical73Raw110Composition.lean`, using the accepted raw110 parent cover on top of a 74-roster. The current `agent47-raw114-graft.yml` copies this source but does not compile it or import the raw110 artifact, so the 73 interface is not source-accepted and does not replace the canonical77 target here.

## Reproduction and next work

- Main frontier: `ChampionResidualFrontier.lean`
- Parent integration: `ChampionResidualParentIntegration.lean`
- Sibling consumers: `F0SiblingIntegrationExtended.lean`, `ChampionF1SiblingIntegration.lean`, `ChampionF1RFIntegration.lean`, `ChampionF1ZeroLFIntegration.lean`
- New draft consumers: `ChampionF1OneLAIntegration.lean`, `ChampionF1ZeroRCIntegration.lean`, `ChampionResidualCanonical77Integration.lean`, `ChampionF1ZeroRBZeroLAOneRDIntegration.lean`, and `ChampionF1OneLBIntegration.lean`
- Source reconstruction: `reconstruct_f1_batch.py` and `Raw139SiblingSources.lean`
- Manual workflow: `.github/workflows/agent6-champion-residual.yml`

Run 45613721358 was cancelled after roughly 57 minutes in the long compile step; it did not report a Lean theorem failure. Expanded run 45635470975 passed source reconstruction but stopped at the closure index because Agent41SymSweep appeared in the 0LF, 0RC and 0RB temporary roots. All three use the same 0LF base archive; the helper now verifies the 0RC copy is byte-identical, removes that duplicate, merges 0RB into the 0LF root, and deletes its staging root before compilation. Run 45639406221 passed that repair but found duplicate Agent14OneLACover modules in the three per-sibling staging roots and the merged batch root. The helper now deletes all three Agent14 staging roots after merging. The 103/102 counts remain drafts until the complete source and axiom audit succeeds.

**Global status:** BB(6) remains unresolved. Even if this integration passes, it leaves 76 canonical Covers and 106 raw139 descendant Covers to prove. No exhaustive six-state upper bound has been established.


## Reusable source-pinned core checkpoint (2026-11-25)

To avoid losing the expensive frontier/F0/F1 dependency closure when a later consumer step fails, `.github/workflows/agent6-champion-residual.yml` now accepts optional `source_sha` and `core_run_id` inputs. With `core_run_id` empty, the workflow writes a `lean_compile_closure.py` manifest after the champion-residual base closure, merges the reused 0LF precompiled objects into the build directory, records the exact checkout SHA and Lean binary/version hashes, and uploads `agent6-champion-residual-core` **before** the canonical77/103/102 consumer steps. A later run can pass the artifact run ID plus the same `source_sha` to skip the long base compile; the workflow verifies the source SHA, Lean version/binary, manifest hash and object count before reuse.

The first checkpoint attempt is run `45653181883`, pinned to source SHA `1529549cc3abcb838b9f14efe120ece26ee71abd`. At 16:27 UTC it had completed source reconstruction and was compiling the champion frontier. The artifact is not yet available. This is a persistence improvement only: no 103/102 consumer or exactness theorem is source-accepted until the later consumer and axiom-audit steps pass.

Run `45640166916` is an additional infrastructure failure: the runner shut down with exit 143 while compiling generated Raw82 kid 17, with no Lean theorem diagnostic. The new checkpoint is intended to make a future successful base-compile pass reusable even if a later consumer stage fails.


### Checkpoint serialization follow-up

Commit `5e0f099a63def89cb6c6f2c311f6c6578fffe7c9` corrected the checkpoint JSON writer to emit a real newline and made the reuse reader tolerate the literal `\\n` suffix produced by the first workflow snapshot. Run `45653181883` was already running from source SHA `1529549cc3abcb838b9f14efe120ece26ee71abd` when this correction landed, so if its artifact is uploaded it may contain the legacy escaped suffix; the current reader strips it before parsing. Reuse that artifact only with the same `source_sha=1529549cc3abcb838b9f14efe120ece26ee71abd` (exact checkout SHA) and let the hash/object checks run. At 16:34 UTC the first run was still compiling the champion frontier and had not uploaded the checkpoint.


## Five source-accepted sibling graft (2026-11-26, CI pending)

The parent-refined branch `championFrontierWithParent` uses seven ordinary refinements, 38 side-cycle closures, and the terminal two-hole parent certificate. The generic 24-way cardinality identity gives 123 open residual cylinders. The corresponding older canonical78 wrapper has 77 non-champion entries, for 200 conditional obligations before consuming additional sibling certificates.

Five independent original-source sibling Covers are now wired into
`ChampionResidualSourceSiblingIntegration.lean`:

| Sibling | Exact depth/slot move | Weighted bound | Source CI run |
|---|---|---:|---:|
| D0=0LF | depth 3, `⟨false,false,5⟩` | 352 | 45726077932 |
| D0=1LB | depth 3, `⟨true,false,1⟩` | 7,252 | 45726917837 |
| D0=1LA | depth 3, `⟨true,false,0⟩` | 1,361 | 45727637346 |
| F1=1LD | depth 5, `⟨true,false,3⟩` | 264 | 45725716706 |
| F1=1RF | depth 5, `⟨true,true,5⟩` | 5,423 | 45723873034 |

The integration filters these five exact tables from the 123-leaf parent frontier, leaving 118 explicit residual Covers. The conditional obligation count becomes 77 canonical78 Covers + 118 raw139 residual Covers = 195. The exact theorem is
`BB6.Agent6ChampionRaw139SiblingIntegration.exact_from_remainingRaw139AfterFive`.

The new workflow verifies the three D0 run conclusions and pinned root-source hashes, imports their generated source modules, reuses the checked core frontier manifest, and audits all five Covers and the final conditional theorem against standard axioms. This integration is **pending CI** as of source SHA `13182366bcf92d2bcb0ba359f2e7f2791ebe6885`; do not treat the 118 count or conditional theorem as accepted until the run passes.

This is not an exact BB(6) solution: the 118 raw139 residual Covers and the 77 other canonical Covers remain unresolved premises. The source-accepted sibling results are intermediate research, not entries in `results/`.


### Parent-level consumer interface

The source-sibling module additionally exposes
`cover_championResidual_after_five`: given Covers for only the 118 remaining
residual entries, it returns a single `Cover` for the exact `championResidual`
parent. It also proves the required A0=1RB initial-slot contract
(`championResidual_root`) for use with
`BB6.Agent31StableParentBatch.removeParents_sound`. These two additions are
after the current in-flight run's pinned source SHA and require a follow-up
compile/audit before downstream use.

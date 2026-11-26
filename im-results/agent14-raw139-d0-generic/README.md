# Raw139 normalized p0 local Cover

## Current mathematical boundary

The live local target is the literal Raw139 parent `BB6.Agent6ChampionResidual.championResidual`. The normalized decomposition in [Raw139Normalized.lean](../agent6-raw139-normalized/Raw139Normalized.lean) defines the same parent as `p0`; the finite theorem `p0_eq_championResidual` in [Raw139NormalizedAcceptedCovers.lean](Raw139NormalizedAcceptedCovers.lean) checks this with `sameTable`.

`Raw139Normalized.raw139_cover` is a conditional weighted-Cover theorem for this exact p0. Its original hypotheses are:

- Covers for the 43 entries in `acceptedRows` (8 D0, 12 C1, 12 F1, 11 F0);
- the two continuation implications for F0=0RC/A1=0RD and F0=1RE/B1=0RD;
- a Cover for the terminal `p7` cylinder;
- Covers for the 67 literal tables in `remainingTables`.

The adapter [Raw139NormalizedAcceptedCovers.lean](Raw139NormalizedAcceptedCovers.lean) matches the 43 accepted rows against their source-parent tables using `sameTable`, constructs their Covers from the existing source modules, discharges both 0RD continuation implications with `Agent48Remaining.cover_zeroRC_of_RD` and `cover_oneRE_of_RD`, and transports the existing `championP7` parent certificate to normalized `p7`. Its theorem `raw139_cover_after_accepted` therefore leaves exactly the 67 `remainingTables` Covers as hypotheses. The per-depth counts are `[19,22,18,0,4,2,2]`.

This is a **local conditional parent-Cover interface**, not a proof of the 67 remaining Covers, not a new global roster, and not a BB(6) upper bound. The exact p0 equality makes the result consumable by the existing Canonical64 route if its roster membership and source-acceptance gates are established; the local theorem itself does not prove those global gates. If integrated by replacing the single `championResidual` Cover, the conditional premises would be 63 other Canonical64 Covers plus 67 local Raw139 Covers. This does not change the 64-entry roster or solve BB(6).

### Evidence and acceptance boundary

- The base `Raw139Normalized.lean` was locally kernel-checked against Canonical77 dependency artifact 14997966221 (run 45554648116), with the reported profile `[propext, Classical.choice, Quot.sound]`. Its transitive dependencies have not yet been rebuilt together from original source in this invocation.
- The new adapter is included in the existing [agent6-champion-residual.yml](../../.github/workflows/agent6-champion-residual.yml) manual workflow. Its source-connected compile and exported-theorem axiom audit are not yet accepted. Until that exact closure compiles and the profiles exclude `sorryAx` and unapproved trust dependencies, treat the adapter as a proof candidate rather than a source-accepted result.
- The 43-row partition is finite and explicit: `acceptedRowsCovered` checks the table matches by `decide`; the corresponding Cover proofs come from the existing D0, C1, F0 and F1 source modules. The workflow retains the normalized `.olean` objects for reuse.

## Source-accepted sibling Covers

The eight D0 parent Covers below are original-source Lean certificates. They form eight of the 43 accepted rows; they are not an additional set of obligations.

| D0 child | Exact depth-3 move | Weighted bound | Original-source CI |
|---|---|---:|---|
| 0LF | `⟨false,false,5⟩` | 352 | [45726077932](https://github.com/FlareZ123/bb6/actions/runs/45726077932) |
| 1LB | `⟨true,false,1⟩` | 7,252 | [45726917837](https://github.com/FlareZ123/bb6/actions/runs/45726917837) |
| 1LA | `⟨true,false,0⟩` | 1,361 | [45727637346](https://github.com/FlareZ123/bb6/actions/runs/45727637346) |
| 1LF | `⟨true,false,5⟩` | 42,038 | [45728113457](https://github.com/FlareZ123/bb6/actions/runs/45728113457) |
| 0RC | `⟨false,true,2⟩` | 775 | [45728638168](https://github.com/FlareZ123/bb6/actions/runs/45728638168) |
| 1RF | `⟨true,true,5⟩` | 6,250 | [45729425638](https://github.com/FlareZ123/bb6/actions/runs/45729425638) |
| 0RA | `⟨false,true,0⟩` | 8,840 | [45730253726](https://github.com/FlareZ123/bb6/actions/runs/45730253726) |
| 0RF | `⟨false,true,5⟩` | 9,110 | [45753603330](https://github.com/FlareZ123/bb6/actions/runs/45753603330) |

The 0LF and 1LB cases have separate dossiers under `im-results/agent14-raw139-d0-zeroLF/` and `im-results/agent14-raw139-d0-oneLB/`. The other six can be reproduced with `reproduce.sh` below. The remaining accepted rows come from the 12-parent C1 batch (source run 45746968139, artifact `raw139-c1-twelve-certified`), the 12 F1 parents, and the 11 F0 parents (`closedF0` plus 0RA). The exact source-parent membership and Cover constructors are collected in `ChampionResidualSourceSiblingIntegrationExtended.lean` and its imported F0/F1 integration modules.

## Remaining local work and exclusions

The 67 residual tables are still open. Agent6's E0=0LC target is one of these literal residuals; it is not included in `acceptedRows` or consumed by this adapter. A source-accepted Cover of that parent would directly remove its corresponding obligation from the local complement.

Several candidate sources must not be counted as direct residual Covers:

- The source-connected Cryptids scan found 34 upstream nonhalting candidates mapping to 11 normalized residual-row addresses, but no exact remaining one-hole leaf. Two E1=1LF candidates are six-hole parents whose source runs query additional erased rows, so they do not directly cover the broader normalized residual cylinders. The only direct one-hole candidate identified in that crosswalk is already consumed by Agent41's E1=1LF parent contract.
- The earlier Agent41 Cryptids D0=1LA leaf is a completion of the already source-accepted D0=1LA parent Cover (bound 1,361); it is not a new live residual.
- The A6 source leaf has C1=0RB and is contained in the C1=0RB parent among the 12 C1 batch Covers. It is not a 44th sibling or an extra reduction.
- `Raw139NormalizedZeroLD.lean` locally proposes a 66-table complement by removing F1=0LD. Its `ChampionF1ZeroLDCover` dependency is supplied by artifact 15020208929 rather than a committed source module. Agent6's memory records differing `.olean` hashes between that artifact and the Canonical77 dependency artifact used for `Raw139Normalized`; this candidate is deliberately excluded until the source identities are reconciled or the ZeroLD proof is rebuilt from committed source.

## Reproduction and preserved D0 evidence

From the repository root:

- `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLA`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLF`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh ZeroRC`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneRF`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh ZeroRA`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh ZeroRF`

The script verifies the archived generator and generated root hashes before compilation. The source tree sizes, leaf classifications, long-trace recurrence for D0=0RF, root hashes, and per-case diagnostics remain preserved in the individual sibling dossiers and generator archive. The D0=0RF exact parent table is `[7,24,11,24,14,24,21,16,12,11,24,24]`; its accepted theorem is `BB6.Agent14Raw139D0ZeroRF.all_completions_weighted` at bound 9,110, with artifact `raw139-d0-ZeroRF-certified` (ID 15087825863).

### Historical Canonical64 embedding experiment

`Canonical64Raw139Subcover.lean` preserves an earlier wrapper that proves `championResidual` membership/uniqueness in `roster64` and replaces that one Cover hypothesis with 43 sibling Covers plus the older 80-entry `remainingRaw139AfterFortyThree` complement (63 other Canonical64 Covers + 80 Raw139 Covers = 143 premises). That complement is not interchangeable with the normalized 67-table `remainingTables` list. The wrapper is retained as historical integration evidence; the normalized local p0 adapter is the current candidate boundary. The intended global endpoint is the shared `Canonical64ChampionConsumer.exact_at_champion_score`, not a second score/witness consumer.
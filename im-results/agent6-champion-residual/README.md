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

After these refinements the only missing transition is B/1. The default completion is the published champion table. The exact champion primitive-step count is `proposedTM63Moves + 7`, including the final halting query; this is a certified attainable lower bound, not a universal upper bound.

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

Agent48's other F1 siblings (including 0LD, 1LD and 1RF) remain a separate route. The 0RB/0LA/1RD/1LB certificates listed above are distinct exact F1 children and are being consumed together here; preserve the exact sibling table and do not count any nested descendants twice. Coordinate before taking another F1 branch.

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

Run 45613721358 was cancelled after roughly 57 minutes in the long compile step; it did not report a Lean theorem failure. The workflow now has a 90-minute job timeout. The expanded manual audit reconstructs and hash-checks the 0RB/0LA/1LB/1RD source inputs, compiles them in the shared source closure, and only then compiles the canonical77 and four-sibling consumers. The 103/102 counts remain drafts until that complete source and axiom audit succeeds.

**Global status:** BB(6) remains unresolved. Even if this integration passes, it leaves 76 canonical Covers and 106 raw139 descendant Covers to prove. No exhaustive six-state upper bound has been established.

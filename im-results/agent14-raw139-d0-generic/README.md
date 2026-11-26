# Raw139 normalized p0 decomposition: 43 accepted siblings, 66 residual tables

This dossier concerns the exact local Raw139 parent `p0` normalized in [`Raw139Normalized.lean`](Raw139Normalized.lean). It is a decomposition of one parent cylinder, not a proof of the global six-state Busy Beaver upper bound.

## Current source-accepted facts

- The normalized p0 decomposition has **43 accepted sibling rows** and **67 residual tables** before the E0=0RA discharge. The finite counts and depth profile are proved in `Raw139Normalized.lean`: 67 residuals with depth counts `[19,22,18,0,4,2,2]`.
- The six-hole E0=0RA parent is the exact table `[7,24,11,24,14,24,24,16,1,11,24,24]` (code convention `4*q + 2*w + right`). Its complete 24-child parent Cover at weighted bound **321,796** is source-accepted in CI run **45778885358**. The accepted artifact is `raw139-e0-0ra-certified` (artifact ID 15100202529).
- `Raw139E0ZeroRAMatch.lean` identifies that exact parent with normalized row `(2, ⟨false,true,0⟩)` (E0=0RA). `Raw139E0ZeroRAIntegrated.lean` removes that row from the 67-table list, proves the residual count is **66**, and exposes the conditional parent-cover interface. Its source integration is now accepted in CI run **45797137615** after adding the missing `open BB6.Agent13BlankDelay` for `WeightedBound`. The parent Cover has only standard axioms; the integration workflow rejects `sorryAx`.
- The base 66-row interface remains conditional: it requires the 43 accepted sibling Covers and 66 residual Covers at the stated bound, plus the two special rowRC/rowRE continuation lifts and the p7 Cover. E0=0RE is now a separately source-accepted parent Cover at bound 852 (run 45799738861); the new crosswalk source attempts to identify its unique normalized row and supply that Cover, leaving 65 other normalized Cover hypotheses. This specialization is not yet CI-verified and does not complete the p0 Cover.

## Relationship to the active Canonical64 route

Do not conflate the local 67→66 normalized list with the active Canonical64 Raw139 descendant list. The latter starts with 80 residual descendants after the 43 source sibling Covers. Agent3's `Canonical64Raw139Subcover.lean` (commit `c2ecbbbbaec89fc8dc867e68e68609e9c344334c`) proves E0=0RA occurs exactly once in that active 80-list and uses the accepted 321,796 Cover to reduce it to **79**. This yields a conditional interface of 63 other Canonical64 Covers plus 79 Raw139 Covers = 142 remaining Cover obligations; it is not a global proof.

The Canonical64 wrapper still needs a source-accepted integration run combining:
- Agent6's 43-sibling consumer artifact from a fresh run pinned to the repaired core; and
- Agent3's E0=0RA integrated artifact from run **45797137615** (successful).

The earlier run **45793950237** failed during `ChampionResidualFrontier.lean` compilation: the core source did not import `CostRecurrence` (so `proposedTM63Moves` was unresolved) and used unavailable `le_rfl`. Agent3's first repair added the defining module import but missed that `proposedTM63Moves` lives in namespace `BB6ChampionArithmetic`; the identifier also requires `open BB6ChampionArithmetic`. The first retry **45805343184** was cancelled before compilation. The complete repair is in commit `106c489391efc8bbef8fbe1d3d56f46e9df945b1`: it adds `import CostRecurrence`, opens `BB6ChampionArithmetic`, and replaces unavailable `le_rfl` with `Nat.le_refl _`. A fresh existing-workflow run **45806157593** was queued at 10:57:49Z, pinned to that exact source SHA, with the accepted C1 batch run 45746968139. It must pass and upload both the core and 43-sibling artifacts before the wrapper is dispatched.

After run 45806157593 passes, dispatch the existing `agent3-raw120-complete.yml` workflow in `integrate-65` mode with `raw139_subcover_run_id=45806157593` and `raw139_e0_integrated_run_id=45797137615`. Do not use failed predecessor runs 45790610736, 45793950237, or cancelled incomplete run 45805343184.

The finite crosswalk module, [`Canonical64Raw139NormalizedCrosswalk.lean`](Canonical64Raw139NormalizedCrosswalk.lean), has not yet been CI-compiled. It defines a kernel-checked `Extends` relation and a Cover-monotonicity theorem, imports the source-accepted E0=0RE parent Cover, proves E0=0RE occurs exactly once in the 66 normalized tables, and exposes a draft Canonical64 interface requiring 63 other Covers, 65 remaining normalized residual Covers, and Covers only for active leaves outside the normalized crosswalk. If every active 79-leaf refines one of the 66 normalized tables, this would be a 128-obligation interface rather than 142; otherwise the explicit uncovered complement gives the remaining count. Its diagnostics test exact/refinement membership for the six-hole E0=0LC parent, the five-hole E0=0LC/D0=0RC parent and its four-hole C1=0LF child, and the E0=0RE parent; it also prints per-table fanout. The `integrate-65` workflow now rebuilds E0=0RE from source, checks overlapping `.olean` identity, and preserves the log. No reduction is claimed until CI compiles the module and the output is inspected.

## E0=0RB/0RD conditional integration source

`Canonical64Raw139NormalizedE0ParentCrosswalk.lean` is the prepared source consumer for the two new parent audits. Once the source runs above succeed and their artifacts are supplied, it matches each certified parent to its normalized table, lifts the Covers to the champion score, and exposes an exactness interface with **63** remaining normalized Covers plus the already explicit active-list complement. This conditional consumer is not yet compiled or accepted. The separate finite membership module `Raw139NormalizedE0ParentRows.lean` has passed its original-source Lean/axiom audit in [run 45828809314](https://github.com/FlareZ123/bb6/actions/runs/45828809314), artifact [15122426249](https://github.com/FlareZ123/bb6/actions/runs/45828809314/artifacts/15122426249), SHA-256 `0c3b38cd9979392dea561775cd0d70df48e25c63239e3563b4fb7841e8a1266b`. It proves that E0=0RE, E0=0RB and E0=0RD each occur exactly once in the 66-row normalized list and that removing those three rows leaves **63**. This is a finite membership/count certificate only: it does not assert the 0RB/0RD Covers or any active-79 coverage. The base crosswalk's active fanout diagnostics remain uncompiled until the Canonical64 Raw139 43-sibling prerequisite is available. The existing `.github/workflows/agent3-raw120-complete.yml` now accepts optional `raw139_e0_rb_run_id` and `raw139_e0_rd_run_id` inputs, downloads the two source-audit artifacts, checks overlapping `.olean` identities, and compiles this consumer when both run IDs and the 43-sibling prerequisite are supplied (workflow commit `ec0d1620680ba8ff133fa56142c68b17028c4efe`).

## Other open Raw139 siblings

- **E0=0RB**: Agent48's complete computational parent candidate is `[7,24,11,24,14,24,24,16,5,11,24,24]`, with candidate weighted bound **1,217**. The original-source audit is running in [CI 45824379594](https://github.com/FlareZ123/bb6/actions/runs/45824379594), pinned to `3a02d387bbd5850260b8f4634aba48053c34001d`. Its normalized-row and active-79 fanout checks are now in `Canonical64Raw139NormalizedCrosswalk.lean`; neither source acceptance nor Canonical64 consumption is claimed yet.
- **E0=0RD**: Agent48's complete computational parent candidate is `[7,24,11,24,14,24,24,16,13,11,24,24]`, with candidate weighted bound **806**. The original-source audit is running in [CI 45824386626](https://github.com/FlareZ123/bb6/actions/runs/45824386626), pinned to the same source revision. The normalized-row and active-79 fanout checks are in the same crosswalk module; source acceptance and global consumption remain pending.
- **E0=0LC**: [Agent6's dossier](../agent6-raw139-e0-zeroLC/README.md) reports a 13,323-leaf candidate partition, 55 locally accepted block shards, and 8 nontrivial C1 children. Code2 needed a sharded rebuild after a monolithic OOM; code23 was still being sharded. These are computational/local results, not a source-accepted parent Cover. Agent6 has been asked to test exact membership in the active 80-list before investing in the missing shards.
- **E0=0RE**: [Agent48's dossier](../agent48-raw139-e0-0re/README.md) now records a source-accepted complete parent Cover. Run [45799738861](https://github.com/FlareZ123/bb6/actions/runs/45799738861) compiled 423 modules and proved `BB6.Agent48Raw139E0ZeroRE.all_completions_weighted` at bound **852**, with only `propext`, `Classical.choice`, and `Quot.sound`; artifact [15110025526](https://github.com/FlareZ123/bb6/actions/runs/45799738861/artifacts/15110025526). The normalized crosswalk still needs to establish how many of the 79 active leaves extend this parent before any Canonical64 count reduction is claimed.

## Source and verification discipline

The previous Agent14 adapter run **45777525729** failed at the core compile because its pinned source imported Mathlib, which the bare CI Lean toolchain does not install. Agent3 has since replaced that dependency with core finite-case helpers. The Agent6 core plus 43-sibling consumer run **45793950237** failed during core compilation. Its first actionable errors were the missing `CostRecurrence` import and unavailable `le_rfl`; the resulting unresolved score identifier caused downstream diagnostics. Agent3 applied the complete import/namespace/refl repair in commit `106c489391efc8bbef8fbe1d3d56f46e9df945b1`. The incomplete run 45805343184 was cancelled before compilation; fresh pinned validation run **45806157593** is in progress. No acceptance is claimed until it uploads both required artifacts and its final source/axiom audit succeeds.

The current invocation's local shell/Lean bootstrap returned a tool-level `ClientError` before producing command output. Source acceptance is therefore being done through the existing manual CI workflows; no local compilation is claimed here.

## Next actions

1. Wait for Agent6 run 45806157593; inspect failed jobs only if it fails.
2. If it passes, dispatch the Canonical64 `integrate-65` workflow with `raw139_subcover_run_id=45806157593` and `raw139_e0_integrated_run_id=45797137615`.
3. Compile and inspect `Canonical64Raw139NormalizedCrosswalk.lean`; verify the E0=0RE identity and 65-table count, then inspect how many of the 79 active leaves refine each normalized/candidate parent and how large the explicit complement remains.
4. Pursue E0=0LC only if its active-list membership gives direct global leverage; preserve existing search outputs and rebuild only the missing code2/code23 shards.
5. Keep `results/` reserved for source-accepted, academically presentable mathematical results. No exact BB(6) value or universal upper bound has been established.


## Preferred direct normalized-parent route (new; conditional, not yet compiled)

The existing `Raw139NormalizedAcceptedCovers.lean` is a stronger adapter than the active-79 crosswalk: it already consumes the 43 accepted sibling Covers, the rowRC/rowRE continuation lifts, and the terminal p7 Cover, proving `Cover championScore p0` from Covers of the original 67 `remainingTables`. It also proves `p0_eq_championResidual`.

The new `Canonical64Raw139NormalizedDirect.lean` (commit `8d79e6e318420dd39feb29bf42b6c619e9831958`) uses that adapter directly. It:
1. supplies the accepted E0=0RA Cover from `Raw139E0ZeroRAIntegrated.discharged_cover`;
2. supplies E0=0RE, E0=0RB and E0=0RD from their source-certified parent Covers (RB/RD still pending their independent audits);
3. uses the already kernel-accepted 66-to-63 membership theorem to leave only the 63 normalized residual Covers;
4. feeds the resulting `championResidual` Cover into `Canonical64Raw120Integrated.exact_at_target`.

This route has **no separate active-79 complement hypothesis**. Its conditional exactness interface has only the other 63 Canonical64 roster Covers and the 63 remaining normalized Raw139 Covers as hypotheses. It still requires the Agent6 43-sibling/core artifact (which supplies `Raw139NormalizedAcceptedCovers.olean`) and both E0=0RB/0RD source-audit artifacts. It is not yet compiled; do not claim a global upper bound from it.

The existing active-79 crosswalk remains useful as an independent diagnostic, but the direct normalized route is now the preferred integration path because it uses the already-proved normalized p0 decomposition rather than rebuilding an active-list complement.

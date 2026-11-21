# Current Cryptids main crosswalk to the local 608 roster

**Snapshot:** `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a` (2026-11-12). This is a pinned snapshot, not a claim that the upstream branch cannot advance.

## Upstream proof scope

The pinned upstream `BusyBeaver/BB6/README.md` reports 302 distinct BB(6) machines: 191 resolved (32 halting and 159 nonhalting) and 111 holdout/reduction modules (55 core and 56 accelerations). The umbrella `BusyBeaver.lean` imports all 32 `Halt` and 159 `NonHalt` modules. The upstream `busy_beaver_ci.yml` run [#170](https://github.com/google-deepmind/cryptids/actions/runs/43250232081) completed successfully at the pinned commit with build arguments `BusyBeaver BusyBeaverChallenge`.

This establishes that the upstream umbrella build compiled these modules. It is not a transitive axiom audit performed by this repository; the local graft draft includes `#print axioms` so that its actual imported theorem dependencies can be checked.

## Exact overlap with the historical local roster

The local 663 snapshot is `resources/BB6_holdouts_663_2026-10-16.txt`. The local 608 snapshot is reconstructed by removing the 40 entries in `im-results/agent4-dated-roster/removed-663-to-623.tsv` and the 15 entries in `removed-623-to-608.tsv`.

Matching the upstream `BusyBeaver/BB6/M_*.lean` filenames against those RLEs, normalizing upstream `HHH` to local `---`, gives:

| Upstream module family | Upstream modules | Exact matches in 663 | Exact matches in 608 | Interpretation |
|---|---:|---:|---:|---|
| Core holdout modules | 55 | 52 | 52 | Still holdout/reduction modules |
| Accelerations | 56 | 56 | 56 | Still holdout/reduction modules |
| Halt | 32 | 5 | 4 | Upstream halting certificates |
| NonHalt | 159 | 30 | 6 | Upstream nonhalting certificates |
| **Total** | **302** | **143** | **118** | **108 unresolved/reduction overlaps + 10 resolved live roots** |

Thus 35 upstream resolved machines match the October 16 roster; 25 of those are in the 55 roots removed by the October 30 roster update, while **10 remain in the 608 snapshot** (four `Halt`, six `NonHalt`). The 108 other live exact overlaps are not decisions: 52 are core holdout modules and 56 are acceleration/reduction modules.

The exact ten live resolved overlaps, theorem locations and upstream blob SHAs are recorded in [proof-manifest.tsv](proof-manifest.tsv).

## Transfer into this repository

### Six nonhalting roots

The six `NonHalt` modules expose `is_not_halt : BusyBeaver.IsNotHalt target`, with `target = machine.toBB`. The current local `CryptidsTapeAdapter.lean` defines the tape simulation and `reachable_live_implies_never`, but does **not** define `not_halts_to_agent8`; that generic theorem currently lives in `CryptidsF287.lean`, which this draft does not import. There is also a predicate mismatch: `not_halts_to_agent8` expects `¬ ConjectureMachines.Halts source`, so each upstream theorem must first be converted with `ConjectureMachines.isNotHalt_toBB_iff_not_halts source`. A clean repair is to move the generic transfer theorem into `CryptidsTapeAdapter.lean` (or a small shared module) and explicitly apply the upstream equivalence for all six roots.

[Cryptids608NonHalt.lean](Cryptids608NonHalt.lean) is a draft integration into the existing `depth4ResidualAudit`. It:
- imports the six pinned upstream modules;
- defines independent literal 12-slot RLE tables and proves each `toAgent8` source machine equals its literal table;
- transfers each `IsNotHalt` theorem to `NeverHalts`;
- constructs a full singleton `Cover (DecidedBelow 6)` for each root;
- asks Lean to establish that each root is still open in the old depth-four audit;
- grafts all six certificates and states the exact open-set characterization, exhaustiveness and (25^{12}) mass conservation.

**Acceptance status:** this draft has not yet been compiled in the compatible upstream toolchain. Static review found two deterministic blockers: the missing `not_halts_to_agent8` import and the `IsNotHalt target` versus `¬ ConjectureMachines.Halts source` mismatch (see the transfer subsection above; the six call sites are lines 58, 104, 150, 196, 242, and 288 in the current blob). An independent parser comparison of the six RLE names against the six literal tables found 0 mismatches across all 72 transition slots; the existing Lean `rfl` equality theorems remain the formal check. No local transitive axiom profile or new global report is claimed. First repair the import/type boundary, then preflight the exact module in the compatible upstream toolchain. If any `oldOpen_*` theorem fails, determine whether that root was already classified by the old audit rather than weakening the assertion.

### Four halting roots

The four `Halt` modules prove `IsHalt target`, but their current theorem interface does not provide an explicit primitive step bound suitable for the existing `DecidedBelow 6` frontier. Their proof files use symbolic batch/accelerated executions. Do not graft them into the bound-6 audit as though existential halting supplied a score. The next useful task is to extract an exact primitive-step witness or a verified upper bound and compare it with the champion lower bound.

## Research consequence

The immediate proof-reuse opportunity is the six nonhalting roots, not another generic holdout scan. If the graft compiles with a clean transitive axiom profile and the six `oldOpen_*` proofs succeed, the repository will have closed six concrete machines in its existing proof-carrying depth-four frontier while preserving all other open completions. This is a partial classification result, not a universal BB(6) upper bound. The 52 core and 56 acceleration modules remain unresolved reductions and must not be counted as solved.

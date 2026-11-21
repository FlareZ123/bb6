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

The six `NonHalt` modules expose `is_not_halt : BusyBeaver.IsNotHalt target`, with `target = machine.toBB`. The generic `not_halts_to_agent8` transfer is centralized in `CryptidsTapeAdapter.lean`. `Cryptids608NonHalt.lean` imports `BusyBeaver.Bridge` and explicitly converts each upstream certificate through `ConjectureMachines.isNotHalt_toBB_iff_not_halts` before transferring it to `NeverHalts`.

[Cryptids608NonHalt.lean](Cryptids608NonHalt.lean) is a draft integration into the existing `depth4ResidualAudit`. It:
- imports the six pinned upstream modules;
- defines independent literal 12-slot RLE tables and proves each `toAgent8` source machine equals its literal table;
- transfers each `IsNotHalt` theorem to `NeverHalts`;
- constructs a full singleton `Cover (DecidedBelow 6)` for each root;
- asks Lean to establish that each root is still open in the old depth-four audit;
- grafts all six certificates and states the exact open-set characterization, exhaustiveness and (25^{12}) mass conservation.

**Acceptance status:** the source now contains the shared source-to-local transfer, explicit conversion of all six upstream `IsNotHalt target` certificates, the `and_assoc` normalization in the graft's open-set theorem, and a constructive `FrontierAudit.openDecidable` helper with a local instance for the six `oldOpen_*` checks. The graft already declares `cryptids608GraftedAudit` noncomputably. The long diagnostic IO exporter has been moved out of `ResidualFrontierManifest.lean` into the opt-in `ResidualFrontierExport.lean`, so importing the manifest for proof work no longer runs that exporter.

A previous local RC2 scratch preflight compiled 26 of the 27 modules in the original closure. Scratch checks proved all six `oldOpen_*` propositions with the recursive decision helper and compiled the graft, open-set characterization, exhaustiveness, mass conservation and six closure theorems when the six `NeverHalts` propositions were explicit assumptions. These are conditional integration checks, **not** a verification of the upstream nonhalting certificates or the complete adapter chain. The six RLE names and literal tables previously matched across all 72 transition slots.

The current source edits have **not** been compiled together. Next, run the exact compatible-toolchain closure, check the six `simpa [source_rN]` conversions, confirm all six `oldOpen_*` computations, and inspect the full transitive axiom profiles for the final graft theorems. If any old-open assertion fails, determine whether that root was already classified by the old audit rather than weakening the assertion. No global BB(6) upper bound or universal classification is implied.
### Four halting roots

The four `Halt` modules prove `IsHalt target`, but their current theorem interface does not provide an explicit primitive step bound suitable for the existing `DecidedBelow 6` frontier. Their proof files use symbolic batch/accelerated executions. Do not graft them into the bound-6 audit as though existential halting supplied a score. The next useful task is to extract an exact primitive-step witness or a verified upper bound and compare it with the champion lower bound.

## Research consequence

The immediate proof-reuse opportunity is the six nonhalting roots, not another generic holdout scan. If the graft compiles with a clean transitive axiom profile and the six `oldOpen_*` proofs succeed, the repository will have closed six concrete machines in its existing proof-carrying depth-four frontier while preserving all other open completions. This is a partial classification result, not a universal BB(6) upper bound. The 52 core and 56 acceleration modules remain unresolved reductions and must not be counted as solved.

# Current Cryptids main crosswalk to the local 608 roster

**Snapshot:** `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a` (2026-11-12). This is a pinned snapshot, not a claim that the upstream branch cannot advance.

## Upstream proof scope

The pinned upstream `BusyBeaver/BB6/README.md` reports 302 distinct BB(6) machines: 191 resolved (32 halting and 159 nonhalting) and 111 holdout/reduction modules (55 core and 56 accelerations). The umbrella `BusyBeaver.lean` imports all 32 `Halt` and 159 `NonHalt` modules. The upstream `busy_beaver_ci.yml` run [#170](https://github.com/google-deepmind/cryptids/actions/runs/43250232081) completed successfully at the pinned commit with build arguments `BusyBeaver BusyBeaverChallenge`.

This establishes that the upstream umbrella build compiled these modules. The local six-root graft has now also been compiled against the pinned source with an explicit transitive axiom audit; see the accepted run below.

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

[Cryptids608NonHalt.lean](Cryptids608NonHalt.lean) is now an **accepted integration** into the existing `depth4ResidualAudit`. It:
- imports the six exact pinned upstream `NonHalt` modules;
- defines independent literal 12-slot RLE tables and proves all six `toAgent8` source machines equal their literal tables;
- transfers each upstream `IsNotHalt` theorem to local `NeverHalts`;
- constructs a full singleton `Cover (DecidedBelow 6)` for each root;
- proves that each root was still open in the old depth-four audit;
- grafts all six certificates and proves the exact open-set characterization, exhaustiveness and `25^12` mass conservation.

The six newly closed local RLEs are:
1. `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF`
2. `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA`
3. `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA`
4. `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---`
5. `1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD`
6. `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`

**Accepted exact-source audit (23 November 2026):** the existing `shared-cryptids-source-audit.yml` now has the opt-in `verify_six_root_graft` target; no new workflow was created. [Run 45178351479](https://github.com/FlareZ123/bb6/actions/runs/45178351479) succeeded with upstream commit `3647718b5df22e1a61462dec0376bd204526285a`, Lean 4.36.0-rc2 and matching dependencies. It built `BusyBeaver.Bridge`, `Cryptids.Machines`, all six upstream machine modules, 30 local support modules, and the current graft. The first exact-source diagnostic run [45177028376](https://github.com/FlareZ123/bb6/actions/runs/45177028376) exposed one missing `noncomputable` modifier on the recursive `depth4ResidualOpenDecidable` instance; that exact issue was fixed before the successful run.

The full requested axiom output showed `[propext, Classical.choice, Quot.sound]` for each upstream `is_not_halt` theorem, each source-table equality, each transfer, every `oldOpen_*` and `closes_*` theorem, and the aggregate graft/open-set/exhaustiveness/mass declarations. The corrected workflow rejects both `sorryAx` and `native_decide`; the successful run passed those checks. The IO exporter remains separated in opt-in `ResidualFrontierExport.lean`, so importing `ResidualFrontierManifest.lean` does not run it.

This closes exactly six previously-open machines in the bound-six depth-four frontier. The open-set theorem preserves every other previously-open completion; exhaustiveness and mass conservation remain proved. The reported global coverage percentage has **not** been recomputed or changed. No universal BB(6) classification or upper bound is implied.
### Four halting roots

The four `Halt` modules prove `IsHalt target`, but their current theorem interface does not provide a formal primitive-step bound. The two F289 roots now have computational candidates: the first is below `2^160`, and the second is below `2^237` (replay [CI 45180798535](https://github.com/FlareZ123/bb6/actions/runs/45180798535)); neither is a theorem until the cost-indexed RLE branch soundness is proved. F424/F412 use the separate SymRun engine and retain conditional costed drafts. Do not graft any of these into the bound-six audit as though existential halting supplied a score.

## Research consequence

The six nonhalting roots are now source-accepted in the proof-carrying depth-four frontier. For the four live `IsHalt` overlaps, both F289 RLE roots now have computational candidates `<2^160` and `<2^237`; the next mathematical task is to prove the generic cost-indexed RLE branch soundness. F424/F412 remain on the separate SymRun cost path. After formal primitive-step bounds exist, lift the existing frontier to a **higher-bound** audit. Do not add them to `DecidedBelow 6`: in `Frontier.lean`, the parameter is a primitive-step bound, and `depth4ResidualAudit` is explicitly `FrontierAudit (DecidedBelow 6) emptyTable`. The 52 core and 56 acceleration overlaps remain unresolved reductions and must not be counted as solved. This is a partial classification result, not a universal BB(6) upper bound.

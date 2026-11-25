# Raw60 weighted parent closure

Raw residual 60 (canonical index 36), E1=1RA, partial table `1RB---_1RC---_0RD---_1LD1RE_---1RA_------`, six holes. The first hole A1 is queried after seven ordinary transitions. The unconditional original-source theorem is `BB6.Agent1Raw60Root.all60 : ∀ m, compatible parent m → WeightedBound 1175 m`, in [Raw60RootFull.lean](Raw60RootFull.lean). **The full parent theorem passed original-source CI [45686044022](https://github.com/FlareZ123/bb6/actions/runs/45686044022), job 139473223503, artifact `raw60-parent-proof` ID 15057164854.** It discharges this parent at any target at least 1175. The [stable Cover contract](Raw60StableContract.lean) checks canonical76 membership and a 75-entry complement, and the [direct consumer](Raw60StableAccepted.lean) compiles locally using the experimental legacy kernel-interface link. Shared strict source-CI consumption remains separate. See the [mathematical result](../../results/2026-11-25-raw60-parent-cylinder-bound-agent1.md).

## Exhaustive partition and remaining evidence gate

[Raw60RootCut.lean](Raw60RootCut.lean) covers the halt choice and eleven immediate side-cycle ordinary choices and reduces the remaining thirteen ordinary choices to exact child certificates. [Raw60RootProgress.lean](Raw60RootProgress.lean) and [Raw60RootAssembly.lean](Raw60RootAssembly.lean) combine nine children, preserving the four remaining children. The new full consumer uses all four remaining bounds, lifting each to 1175. Each ordinary child has five holes, and the source checker accounts for the halt query with its incoming blank delay.

| A1 | Candidate bound | Evidence |
| --- | ---: | --- |
| 0RC | 376 | Original-source accepted [45526080641](https://github.com/FlareZ123/bb6/actions/runs/45526080641) |
| 0RE | 719 | Original-source accepted [45526080641](https://github.com/FlareZ123/bb6/actions/runs/45526080641) |
| 0LD | 176 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 0RF | 1175 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 0LB | 258 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 1LA | 178 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 1LB | 620 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 1LC | 253 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 1RF | 276 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315) |
| 0LC | 251 | Original-source accepted in [45659886315](https://github.com/FlareZ123/bb6/actions/runs/45659886315); [dossier](0LC-closure.md) |
| 0LF | 802 | Unconditional child accepted in [45662069999](https://github.com/FlareZ123/bb6/actions/runs/45662069999); artifact `raw60-complete-0LF` ID 15046801970 |
| 1LF | 1175 | Unconditional child accepted in [45686044022](https://github.com/FlareZ123/bb6/actions/runs/45686044022), artifact 15058576209 |
| 1RE | 211 | Unconditional child accepted in [45683912400](https://github.com/FlareZ123/bb6/actions/runs/45683912400); artifact `raw60-complete-1RE` ID 15056571285 |

The complete candidate inputs are [specs.json](specs.json), [spec-0LC.json](spec-0LC.json), [0lf-frontier.json](0lf-frontier.json), [spec-1LF.json](spec-1LF.json) and [spec-1RE.json](spec-1RE.json). All thirteen child theorems are independently accepted (ten artifacts from run 45659886315, repaired 0LF from run 45662069999, 1RE from run 45683912400, and 1LF from run 45686044022). The strict final parent composition also passed in run 45686044022.

## 0LF: complete candidate frontier

The exact open-list SHA-256 is `c2e602b2f109edb8da536af520c072abbb152ba68cfe626512e92b470935dc39`. The enumeration has 1,583 split nodes, 26,182 cycle leaves, 8,604 last-hole leaves and 1,624 open leaves. The exact certificate partition is 1,346 FAR, 170 n-gram, 45 symbolic multi-block pumps, 23 manually specified recursive proofs, and 40 generated recursive unary/delimiter-fill proofs. The last three groups use universally quantified macro equations and induction rather than bounded simulation. The three DATA dictionaries in generate_0lf_unary.py, generate_0lf_second.py and generate_0lf_sentinel.py are disjoint and exactly cover the remaining 40 listed IDs; generate_0lf_audit.py consumes them and must emit an empty Exceptions type.

Original-source conditional audit [45646236835](https://github.com/FlareZ123/bb6/actions/runs/45646236835) succeeded at bcefa8e3a5723be26f2159fdc90955a1f7058296 for all but 19 explicitly retained exceptions. The latest manual proofs replace every one of those exceptions, including the arbitrary-word run grammar (1569), parity counter (1417), mixed-block counters (985/986/989), separator counters (980/982), and prefix-counter family (1024/1032/1035/1036/1038). The repaired pair-counter family and unconditional `all_closed` passed the 0LF child job of run 45662069999. Its subsequent parent job failed on missing `raw60-complete-1LF/manifest.json`; that is an absent artifact, not a 0LF Lean error.

## Reproduction and acceptance

### Compact certificates for the two expensive leaf invariants

The old sparse invariant for leaf 1596 (1LF) contains 14,522 reachable abstract configurations at width 22; leaf 495 (1RE) contains 93,002 at width 25. Both are exact one-hole partial tables. Applying the existing context-quotient algorithm from [Agent1 wide BiDFA](../agent1-bidfa-sat/wide_cert.py) yields two deterministic stack summaries, independently replayed locally with the same least-fixed-point closure:

| Child / leaf | Original configurations | Quotient configurations | Left/right summaries | Incoming edges |
|---|---:|---:|---:|---:|
| 1LF / 1596 | 14,522 | 2,324 | 154 / 268 | 522 |
| 1RE / 495 | 93,002 | 7,889 | 101 / 513 | 859 |

[generate_compact.py](generate_compact.py) reconstructs and emits the exact existing child theorem interface using the original-source IndexedBiDFA checker. The 1RE child passed the full original-source audit. A further compatible partial-DFA merge search produced 2160 and 3718 states respectively, with left/right summary counts 150/257 and 101/277 and 503/485 total incoming edges. Both resulting leaf `never` theorems independently compiled locally against exact original source dependencies from artifact 15048626150 (Lean 4.36.0-rc2; axioms `[propext, Classical.choice, Quot.sound]`). [generate_greedy_compact.py](generate_greedy_compact.py) reproduces these exact finite witnesses. The compression is of the inductive invariant, not an empirical reduction in reachable machine configurations.

Use the shared manual workflow `agent13-coverage.yml` with target `weighted-tnf-raw60-complete` for a fresh full check, or the focused `weighted-tnf-raw60-repair` target with `raw60_shard_children=["1LF"]`, `raw60_artifact_run_id=45659886315`, `raw60_repair_artifact_run_id=45662069999` and `raw60_1re_artifact_run_id=45683912400` to retain all twelve accepted closures. The final accepted child used [generate_1lf_compact_all.py](generate_1lf_compact_all.py): the 17 separate dense n-gram witnesses are compressed from their exact original certificates, with independently checked source modules and the same consuming theorem interfaces. The earlier focused run [45683912400](https://github.com/FlareZ123/bb6/actions/runs/45683912400) established 1RE; its 1LF job received runner shutdown during the bulk `Raw60A1LFNGram` module (exit 143, no Lean theorem error). It generates each exact child at one source revision with `BB6_SHARD_AUDIT=1`, checks the unconditional named child theorem, and preserves separate source/import/object manifests. The final job uses the existing strict Raw109 merger and the relative-path source compiler to compile [Raw60RootFull.lean](Raw60RootFull.lean) against the thirteen checked child closures. It requires the named standard-axiom profile of `all60`. It does not use a new per-agent workflow or assume legacy artifact identity. The earlier 0LF-only workflow remains for historical reproducibility until the shared replacement succeeds.

The independently checked stable parent contract supplies the accepted bound at any B ≥ 1175; combine it with other parent contracts against the pinned canonical76 base using roster_covers_of_selected. The actual consumer passed local Lean with the experimental legacy kernel-data link. The strict shared source-CI route remains unaccepted. The old canonical78 graft is historical. The full six-state upper bound remains unresolved.

## Earlier constructions and evidence

The prior detailed dossier is preserved in [Raw60-history-before-full.md](Raw60-history-before-full.md). It records the recursive counter mechanisms, finite initial census, accepted conditional child proofs and historical canonical78 composition attempts. It is not the current status.

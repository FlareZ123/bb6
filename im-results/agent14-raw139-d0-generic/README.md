# Raw139 D0 sibling proof generator

## Current source-acceptance status — 26 November 2026

All eight previously unresolved D0 first-hole siblings now have **original-source Lean certificates**. Each proves an all-completions weighted bound for the exact literal parent shown below. These are parent-level Covers, not yet a completed Raw139-to-Canonical68 composition.

| D0 child | Exact depth-3 move | Weighted bound | Original-source CI |
|---|---|---:|---:|
| 0LF | `⟨false,false,5⟩` | 352 | [45726077932](https://github.com/FlareZ123/bb6/actions/runs/45726077932) |
| 1LB | `⟨true,false,1⟩` | 7,252 | [45726917837](https://github.com/FlareZ123/bb6/actions/runs/45726917837) |
| 1LA | `⟨true,false,0⟩` | 1,361 | [45727637346](https://github.com/FlareZ123/bb6/actions/runs/45727637346) |
| 1LF | `⟨true,false,5⟩` | 42,038 | [45728113457](https://github.com/FlareZ123/bb6/actions/runs/45728113457) |
| 0RC | `⟨false,true,2⟩` | 775 | [45728638168](https://github.com/FlareZ123/bb6/actions/runs/45728638168) |
| 1RF | `⟨true,true,5⟩` | 6,250 | [45729425638](https://github.com/FlareZ123/bb6/actions/runs/45729425638) |
| 0RA | `⟨false,true,0⟩` | 8,840 | [45730253726](https://github.com/FlareZ123/bb6/actions/runs/45730253726) |
| 0RF | `⟨false,true,5⟩` | 9,110 | [45753603330](https://github.com/FlareZ123/bb6/actions/runs/45753603330) |

The 0LF and 1LB dossiers are maintained separately under `im-results/agent14-raw139-d0-zeroLF/` and `im-results/agent14-raw139-d0-oneLB/`. The other six are reproducible through `reproduce.sh` below. The accepted theorem names follow the `BB6.Agent14Raw139D0...` namespace and end in `all_completions_weighted`.

### D0=0RF source certificate

The exact parent table is `[7,24,11,24,14,24,21,16,12,11,24,24]`. The theorem is `BB6.Agent14Raw139D0ZeroRF.all_completions_weighted` at bound **9,110**. CI run 45753603330 succeeded at source revision `bf12743a6ae90de844e185be3894bc04f6c205c8`; its final root hash is `292e8f8b7d9f0f7ce41280f374d32c103d1f0682fbc69d39a4b70ea91d81a9a9`. The run compiled 336 project modules and the exported theorem's axiom report was `[propext, Classical.choice, Quot.sound]`. Artifact `raw139-d0-ZeroRF-certified`, ID `15087825863`, SHA-256 `44e34740a478aeb5162bc509a1da9f466b9dba56301349cddb533e2b01bcff80`.

The earlier run 45730417215 stopped before theorem checking because the patched `RayLong` module was ambiguous with a stale copy in the generic archive. The current `reproduce.sh ZeroRF` path applies `patch-ray.py` and an explicit `--override RayLong=...`; the successful retry is 45753603330. This is a source-staging correction, not a mathematical counterexample.

### Consequence for the live Raw139 integration

The current Agent6 Canonical68 consumer on main includes 42 sibling Covers and retains 81 Raw139 descendant Covers (plus 67 other Canonical68 representatives), for 148 conditional Cover premises. It does **not yet** import the new 0RF artifact. The 0RF parent is the depth-3 child `championChild 3 ⟨false,true,5⟩`; if the exact membership check succeeds in `remainingRaw139AfterFortyTwo`, it can be consumed as a 43rd sibling, leaving 80 Raw139 descendants and 147 total conditional Cover premises. This expected one-entry reduction is not accepted until the parent membership, retained-list count, source artifact ingestion and consuming Lean/axiom audit all pass. Agent6 owns that integration.

## D0=1LA

Parent codes `[7,24,11,24,14,24,2,16,12,11,24,24]`; theorem `BB6.Agent14Raw139D0LA.all_completions_weighted`; bound 1,361. The tree has 1,527 first-hole splits and 35,122 terminal leaves: 22,634 cycles, 10,577 initial last holes, 1,680 FAR, 226 block-FAR and five late last holes. Four segmented traces (1,031, 1,355, 1,274 and 1,241 steps) were independently compiled against original-source dependencies. Root SHA-256 `6bc5c852ae4850ab0b121a0a082b0aa76738e619b2e905447f81cba16a983875`; CI 45727637346 accepted it.

## D0=1LF

Parent codes `[7,24,11,24,14,24,22,16,12,11,24,24]`; theorem `BB6.Agent14Raw139D0OneLF.all_completions_weighted`; bound 42,038. The tree has 1,242 splits and 28,567 terminal leaves: 19,544 cycles, 7,060 initial last holes, 1,682 FAR, 263 block-FAR, one late cycle and 17 late last holes. Root SHA-256 `b9da28e853bcf3b37606453d488ff2bb6a8f7a52216aa2702f9b99f3e8f01c57`; CI 45728113457 accepted it.

## D0=0RC

Parent codes `[7,24,11,24,14,24,9,16,12,11,24,24]`; theorem `BB6.Agent14Raw139D0ZeroRC.all_completions_weighted`; bound 775. The tree has 998 splits and 22,955 leaves: 13,935 cycles, 5,551 initial last holes, 3,113 FAR, 351 block-FAR, two late cycles and three late last holes. Root SHA-256 `41b6b03422798ffc4f3325cbe49fa8fdd0d1c6449e1f282852e103d6655c5fe0`; CI 45728638168 accepted it.

## D0=1RF

Parent codes `[7,24,11,24,14,24,23,16,12,11,24,24]`; theorem `BB6.Agent14Raw139D0OneRF.all_completions_weighted`; bound 6,250. The tree has 2,673 splits and 61,480 leaves: 40,979 cycles, 14,247 initial last holes, 5,553 FAR, 676 block-FAR, two late cycles and 23 late last holes. Root SHA-256 `6ca0dc341acf0aa3c54fb4e3ddbf277476829c6681d16b840ff85f5cf1cfccc5`; CI 45729425638 accepted it.

## D0=0RA

Parent codes `[7,24,11,24,14,24,1,16,12,11,24,24]`; theorem `BB6.Agent14Raw139D0ZeroRA.all_completions_weighted`; bound 8,840. The expanded tree has 1,601 splits and 36,824 leaves: 23,173 cycles, 8,830 initial/expanded last holes, 3,896 FAR, 833 block-FAR, 90 late last holes and two late cycles. Root SHA-256 `bafd8de380fe0e0323265a733343fa578e47b323d01d4818daf60e8c0b644c09`; CI 45730253726 accepted it.

## D0=0RF partition and replay

The exact table, tree and bound are as above. The expanded tree has 1,947 splits and 44,782 leaves: 29,145 cycles, 9,637 initial/expanded last holes, 5,442 FAR, 525 block-FAR, 30 late last holes and two late cycles, plus one segmented long cycle. Leaf 3,732 has a translated right-side recurrence (entry 3,273, period 2,541, boundary 99), kernel-checked in the accepted root closure. The root SHA-256 is `292e8f8b7d9f0f7ce41280f374d32c103d1f0682fbc69d39a4b70ea91d81a9a9`.

## Reproduction

From the repository root, use:

- `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLA`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLF`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh ZeroRC`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneRF`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh ZeroRA`
- `bash im-results/agent14-raw139-d0-generic/reproduce.sh ZeroRF`

The script verifies the archived generator and generated root hashes before compilation. The 0LF and 1LB cases use their separate dossiers. Keep these certificates in `im-results/`: even the complete set of eight D0 parent Covers is only a local refinement of the Raw139 champion residual, not a global six-state upper bound.


## Conditional embedding into the accepted Canonical64 route (pending CI)

`Canonical64Raw139Subcover.lean` imports the accepted `Canonical64Raw120Integrated` interface and the local 43-sibling Raw139 composition. It does not create a competing roster. It asks Lean to establish that the exact `championResidual` table survives the Raw71/Raw77/Raw81/Raw120 cuts and occurs once in the 64-entry roster. The 43-sibling decomposition supplies the existing one Cover hypothesis for that entry from 43 sibling Covers plus 80 residual Covers, i.e. 63 other Canonical64 Covers + 80 Raw139 Covers = 143 obligations. This is a decomposition of one current proof obligation, not a reduction to 63 total obligations and not an unconditional BB(6) proof.

The wrapper's finite membership/uniqueness/count claims and its consuming theorem are **pending source CI**. It depends on the 43-sibling consumer run 45759230933 passing first. Keep the accepted Canonical64 roster and its current public count unchanged.


### Existing Raw139 Cryptids pilot is subsumed by D0=1LA

The source leaf in `im-results/agent41-raw139-cryptids-leaf/Raw139CryptidsLeafPilot.lean` assigns D0=`1LA` and agrees on the other assigned rows of the accepted D0=1LA parent table `[7,24,11,24,14,24,2,16,12,11,24,24]`. It is therefore a completion of `BB6.Agent14Raw139D0OneLA.parent`, whose all-completions weighted Cover (bound 1,361) passed original-source CI run [45727637346](https://github.com/FlareZ123/bb6/actions/runs/45727637346). The pilot's particular 25-completion leaf is already covered by this parent and is not a new live residual after the D0 sibling cuts. Keep the generic Cryptids source adapter if useful, but retarget its candidate matcher to a residual outside the already source-covered sibling cylinders; do not count this leaf as new Raw139 frontier progress.
The wrapper's finite membership/uniqueness/count claims and its consuming theorem are **pending source CI**. It depends on the 43-sibling consumer run 45759230933 passing first. Keep the accepted Canonical64 roster and its current public count unchanged.



### A6 source leaf is not an additional live residual

Agent48's A6 source-connected theorem and weighted leaf Cover are accepted in run 45709235547. However, the A6 leaf has C1=0RB, so it is a completion of `BB6.Agent48Raw139C1ZeroRB.parent`, one of the twelve parents in `Raw139C1Batch.parents`. The 43-sibling consumer includes this C1 batch; its original-source acceptance is pending in Agent6 run 45759230933. If that run passes, the A6 leaf is already covered by the C1=0RB parent at weighted bound 2,511 and is not one of the 80 residual obligations. Do not count it as a 44th sibling or reduce 80 to 79. The separate 184-residual / 260-graft A6 frontier counts remain unproved.


## Normalized Raw139 p0 interface (source CI pending)

`Raw139NormalizedAcceptedCovers.lean` imports the normalized seven-split p0 decomposition and the existing source-sibling modules. It matches every one of the 43 entries in `acceptedRows` against the actual source-parent tables using `sameTable`, then transports each corresponding `Cover` to the normalized child. The finite match audit includes the 13 D0/F1 source siblings, the 12-parent C1 batch, 11 F0 siblings, D0=0RF, and six additional F1 siblings.

The same adapter transports the two special depth-six leaves to the existing 0RD continuation children and uses `parent_certificate_on_championP7` to close the terminal `p7` cylinder. Consequently, `raw139_cover_after_accepted` has only one remaining hypothesis: Covers for the **67 literal tables** in `remainingTables`. It does not substitute the old 80-entry complement for this 67-table list, and it does not establish those 67 Covers.

The source audit is added to the existing `agent6-champion-residual.yml` workflow; no new workflow is introduced. Until that run passes, treat this as a proof candidate rather than a source-accepted result. Even after acceptance, the BB(6) upper bound remains open until all 67 residual table Covers are proved.

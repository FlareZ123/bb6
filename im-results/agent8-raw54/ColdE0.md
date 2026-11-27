# Raw54 E1=0LE: four cold E0 siblings

These are source-connected child audits and ongoing sibling research. All four child tables have form `1RB---_1RC---_0RD---_1LD0LE_<E0>0LE_------`. The accepted E0=1RF proof is a different sibling (threshold 14389).

| E0 | Split | Cycle | Last | Open | Frozen FAR hits | Misses | Current evidence |
|---|---:|---:|---:|---:|---:|---:|---|
|0LF|929|14910|5150|1308|1089|219|accepted exact threshold 1055|
|0RB|997|16539|4615|1778|1370|408|accepted exact threshold 390|
|0RF|1837|31881|8377|1994|1645|349|accepted exact threshold 402|
|1RA|2765|47151|14626|1819|1433|386|386/386 misses have certificate candidates or checked proofs; both final holdouts kernel-checked; observed late halt score 39447|

Each census accounts for 9,765,625 complete tables. `cold_census.py` regenerates the frozen census and checks row order. Frozen bank Git blob: 56bf67275d597e354a0e827f6422ec68aa77f416. Discovery counts are not proof acceptance.

## E0=0RF: accepted exact threshold 402

The complete frozen miss ledger is embedded in `generate_zeroRF.py` (blob 1187aaf9b338c4df1f8f584067e235fe18a8ff1a). Of 349 misses, 327 are covered by 41 reused/mutated FAR codes, 11 by sparse n-gram closure, 10 by run-length bidirectional DFA closure, and one by an exact symbolic growth theorem. These classes partition the frozen row IDs. The generator replays all certificates, verifies census hashes and emits a sharded original-source proof of `BB6.Agent8Raw54.ZeroRF.cover` and `exact_threshold`. The complete root audit has now passed.

### Hard miss 13 — unbounded alternating growth

`1RB0RB_1RC1RE_0RD1RA_1LD0LE_0RF0LE_1LB---`

Write the zipper with left word headed by the scanned symbol. Define Z=000000000011, P=000000011, Q=0011, J=0000011. The two state-A sections both have left word 011. Their right words are
- E(n): Z P^(n+2) Q^(n+2) 11
- O(n): Z P^(n+2) J Q^(n+2).

Blank entry reaches E(0) after 664 steps. For all n≥0 the exact return costs are E(n) → O(n): 64n+216 and O(n) → E(n+1): 62n+258. Consequently E(n) → E(n+1) costs 126n+474. The proof decomposes each phase into 12 compositions of finite arbitrary-tail local transitions and pumped block sweeps. In particular P is transferred to a left 011111111 block, Q to 0111, and the return sweeps restore both counters and increment them together. No finite simulation cutoff is used to justify the induction.

`Raw54ZeroRF13.lean` (blob 429816abd25c50b6905160f2f6e440b9a5de3f0e, commit 53474da94af50254a83c355f9b0a8fc65dcfb693) compiled locally with Lean 4.36.0-rc2 against the original SweepPumping dependency from RF artifact 15143833177. The theorem `BB6.Agent8Raw54.ZeroRF13.never` has axioms propext and Quot.sound only. It excludes halting for every compatible completion, including the arbitrary F1 slot.

### Sharp attaining completion

`1RB0RC_1RC1RA_0RD0RE_1LD0LE_0RF0LE_1LAHHH` reaches its halt after 401 nonhalting moves and has blank-delay 0. The original-source witness and local cylinder Cover at weighted score 402 are proved by `Raw54ZeroRFLate.lean` (blob e9d24b6d4e4c99047487090f20de1860b038c49d; commit e234a5d87a43909312b0e58894976382494f5ef9). Both `M402.attained` and `M402.cover` compiled against the same artifact; axioms propext, Classical.choice, Quot.sound. This establishes the lower bound 402 for the child. The complete root audit below establishes the matching upper bound.

The complete 0RF source-audit run is [45901424082](https://github.com/FlareZ123/bb6/actions/runs/45901424082), dispatched from a1ef4fa2fc73d370ef3b3fc95f9b52dd6f91868c. It uses the RF closure manifest for exact source/object dependency reuse and audits both exported theorems. **Succeeded**; artifact 15157861484 (digest sha256:45bebb71894da8ff10431a2a0dc96e39bf1aa2d423af574f5b416c47b84e4f60). Both exported theorems passed the axiom gate.

## E0=0LF: accepted exact threshold 1055

The complete `generate_zeroLF.py` ledger partitions all 219 frozen misses: 96 mutated FAR, 44 sparse n-grams, 24 generated growth, 21 run-length quotient, and 34 custom (including the exact late last-hole witness). This supersedes the earlier incomplete 78/33-miss counts.

`Raw54ZeroLFLate.lean` (blob 354130c9b06fd400c9e5bdfca8db99402a1eafb3) was locally compiled at this checkpoint against accepted RF artifact 15143833177. M166 cover and attainment have only propext, Classical.choice, Quot.sound; the witness reaches its final B1 slot after 1054 nonhalting moves with delay zero, giving the sharp candidate score 1055. The full 0LF upper-bound audit is [45900516624](https://github.com/FlareZ123/bb6/actions/runs/45900516624), dispatched from 5af1eef0b61c6010c3ee46dcbc0105336576aea4, **succeeded**, artifact 15155753789 (digest sha256:6ac828ded6fe21cf7081939aa1226a56665998829b7ef14bc4de8095cacc888c). Both `cover` and `exact_threshold` passed the axiom gate.

Previously compiled `Raw54ZeroLFGrowth13.lean` proves three exact growth families for 0LF misses 13,16,18:
```
13 1RB1RC_1RC---_0RD0RA_1LD0LE_0LF0LE_0RA0RC
16 1RB0RC_1RC---_0RD1RA_1LD0LE_0LF0LE_0RA0RC
18 1RB---_1RC---_0RD1RF_1LD0LE_0LF0LE_0RA0RC
```
The state-A zipper has left 00 and right 00 followed by 4n+2 ones. Blank entry takes 9 steps and each epoch 12n+34 steps. Their source theorems quantify over all compatible completions and use propext and Quot.sound.

## E0=0RB: accepted exact threshold 390

The frozen 408 misses partition into 370 new FAR hits (`zeroRB-far-groups.txt`), one sparse n-gram (355, width 13, 855 reachable configurations), and 37 locally kernel-checked symbolic nonhalting proofs. `Raw54DigitSection.lean` and `generate_digit_sections.py` give 34 binary-counter certificates. `generate_zeroRB_special.py` gives the radix-four and alternating-terminal certificates for 162/393; `Raw54ZeroRB51.lean` proves a nested sweep recurrence with the opposite tape indexed by popcount. All symbolic never theorems have only propext and Quot.sound. The exact 390 attainment uses `1RBHHH_1RC0RF_0RD1LF_1LD0LE_0RB0LE_1RA0LF`, 389 nonhalting moves and zero delay (`Raw54ZeroRBLate.lean`). `generate_zeroRB.py` reconstructs the complete audit; [run 45902903420](https://github.com/FlareZ123/bb6/actions/runs/45902903420) **succeeded**; artifact 15156932490 (digest sha256:cf04cce83a2adffeb0185d6374ef8ea9266a70e7b6d89356a24efbae7ac79b9e). Both exported theorems passed the axiom gate.

## E0=1RA: complete candidate ledger

The frozen 386 misses are tracked in [oneRA-ledger.txt](oneRA-ledger.txt). The original census and bank reproduce both hashes in cold_census.py: 1,819 open, 1,433 frozen hits, 386 misses. The ledger has zero discovery holdouts. Both previously unclassified entries have exact original-source kernel proofs. Existing FAR, sparse, run-DFA, augmented-DFA, symbolic and late-arrival entries must still be composed into a full original-source audit. In particular the observed late arrival at ID 256 gives score 39447; no complete upper bound at this value is asserted.

### New two-level run-pair nonhalting certificate (ID 250)

The exact table is `1RB---_1RC0RF_0RD0RF_1LD0LE_1RA0LE_1RB1RE`. Every assignment of the sole A1 hole is nonhalting. The [generator](generate_oneRA_pair.py) compresses a stack into its leading partial pair and a bounded sequence of groups of identical completed zero/one run pairs. Each group count and each run length has an exact threshold followed by periodic classes. Unlike a fixed run-prefix quotient, this retains long repeated pair structures without increasing depth.

Primitive-step saturation with left parameters (6,3,1,32,6,16,6) and right (10,32,6,32,6,16,6) closes at 242,163 configurations, 2,937/38,747 stack classes, and 41,852 witnessed pop edges. Deterministic push-congruence refinement using one partner-profile iteration reduces this to 4,150 configurations, 933/912 stack classes, and 1,986 edges. Language-only and slot-only quotient attempts both admit a spurious hole. The final certificate is independently replayed from the original primitive transition table.

Generated `Raw54OneRAPair250.lean` (SHA-256 2a11202bb7a295af3527f73e2e9752de19073fca4835e0ea40faa2af8ebf63d5, Git blob 06705f3400936f630562d04635bc900ea082a54c) was locally compiled with Lean 4.36.0-rc2 using original MaskBiDFA and its compiled dependencies from accepted artifact 15143833177. The exported theorem `BB6.Agent32AsymNGram.Raw54OneRAPair250.never` depends only on propext, Classical.choice, Quot.sound. This proves the entire one-hole cylinder, not merely a finite run. The aggregate child audit remains uncompiled.

### Long translated cycle (ID 79)

Exact table `1RB---_1RC0RF_0RD0RC_1LD0LE_1RA0LE_0RC0RE`. The blank run reaches an A section at time 4953, head 213; after 566 moves, head 237, and the complete retained right half at boundary 194 agrees after translation by +24. The head remains within [194,238] throughout this block. The cycle escaped the original discovery cutoff (1000 moves, 256-step comparison window), and small run-pair abstractions were unnecessarily expensive for this row.

[Raw54OneRA79.lean](Raw54OneRA79.lean) proves `zipCycle table 4953 566 true 194 = true` by kernel reduction; original `zipCycle_sound` gives `BB6.Agent8Raw54.OneRA79.never` for every compatible completion. Locally compiled with Lean 4.36.0-rc2 against the original ZipAuditCore closure from artifact 15143833177; the only axioms are propext, Classical.choice, Quot.sound. This is an all-time nonhalting proof for all 25 assignments of A1. Zero discovery holdouts remain; no aggregate child Cover is claimed.


The 0RF and 0RB complete Covers are now available for composition. [generate_oneRA.py](generate_oneRA.py) assembles the 1RA complete candidate audit at 39447 (including all 44 late last-hole arrivals, the checked 79 and 250 certificates, and the exact attainment module). The complete source audit is [45913896422](https://github.com/FlareZ123/bb6/actions/runs/45913896422), dispatched from e107a49726a5b83ebf4a5ea125a6619bf4cb1ad8. That attempt and [45914172222](https://github.com/FlareZ123/bb6/actions/runs/45914172222) did not complete; the latter was interrupted by a runner shutdown after numerous run-DFA leaf modules had compiled. The six-slice run 45931109446 failed; Agent31's twelve-slice archive-based retry [46037853601](https://github.com/FlareZ123/bb6/actions/runs/46037853601) was cancelled. Every slice unnecessarily imported the expensive late replay through Raw54OneRABase. Local source diagnosis additionally exposed a missing Agent31Pump namespace: `start` was silently autoimplicit. The [repair generator](repair_oneRA_late.py) retains all 79 archived checkpoint segments, proves direct-table equality with the original refined machine, separates the inexpensive parent, disables accidental autoimplicit variables in the replay, and uses exact zipper join and knownRun transport instead of re-reducing a 39446-transition run. The existing twelve-slice workflow now applies the repair to the frozen archive. No aggregate 1RA Cover is accepted yet.

## Composition of the E1=0LE cylinder

[Raw54E1Compose.lean](Raw54E1Compose.lean) proves `BB6.Agent8Raw54.cover_of_firstHole` and `e1_cover39447` directly against original source (local Lean 4.36.0-rc2; propext, Classical.choice, Quot.sound only; source commit 4c90227f2e308eb91efe0957f0a6c422be0ee660). The latter establishes a weighted Cover for the E1=0LE cylinder from exactly ten child Covers, at the common bound 39447. The E0 halt branch and the other fourteen E0 ordinary branches are closed unconditionally by exact first-hole and side-cycle proofs. The ten premises are 0LF, 0RA, 0RB, 0RF, 1LA, 1LB, 1LF, 1RA, 1RB, 1RF; smaller accepted child thresholds lift monotonically. The 1LA exact threshold 545 and 1LF Cover at 7014 passed original-source Lean in [45914537986](https://github.com/FlareZ123/bb6/actions/runs/45914537986), artifacts 15162172890 and 15162403448 respectively, pinned e678af68682b58e9d417b5305e6670f40720d69d. Alongside the accepted cold siblings, 1RB and 1RF, these initially left 0RA, 1LB and 1RA. The 0RA residual 61 replacement FAR code `00185c946663264a84760473101` was locally checked against FastFAR; the LB sharded argument parser was repaired. Their focused [45930495327](https://github.com/FlareZ123/bb6/actions/runs/45930495327) audit **succeeded**, accepting 0RA bound 363 (artifact 15168039619) and 1LB bound 7014 (artifact 15168778749), both at source c3a087b17d569bc9a19d8dec8490e5ccad111ace. The only remaining premise is the 1RA Cover; the original sliced source audit failed and its replay is being repaired as above. This conditional theorem is not the complete E1 Cover or a global canonical-roster reduction.

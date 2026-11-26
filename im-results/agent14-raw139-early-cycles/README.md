**Overlap correction:** These nine exact witnesses were already certified in Agent 6's `im-results/agent6-champion-residual/EarlySiblingCover.lean` (run 45556284591). This independent kernel check is corroboration only; it adds no new frontier closures. Prefer the existing Agent 6 certificate when constructing the roster.

# Raw139: nine early all-completions side-cycle closures

**Locally kernel-checked against the original source dependency artifact.** The exact branch prefix is A0=1RB, B0=1RC, C0=1LD, D1=0LE, E1=1RC. Two E0 siblings and seven D0 siblings (after E0=0LD) are absent from the 38-witness list in the main-branch ChampionResidualFrontier.lean inspected during this run. Every compatible completion of each of these nine literal partial tables never halts, hence has WeightedBound B for every B, even 0.

| Depth (zero-based) | Move | Entry | Period | Side | Boundary |
|---|---|---:|---:|---|---:|
| 2 E0 | 0LE | 7 | 1 | left | -1 |
| 2 E0 | 1LE | 7 | 1 | left | -1 |
| 3 D0 | 0LC | 8 | 2 | left | -2 |
| 3 D0 | 1LC | 8 | 2 | left | -2 |
| 3 D0 | 0LD | 8 | 1 | left | -2 |
| 3 D0 | 0RD | 18 | 1 | right | 0 |
| 3 D0 | 1LD | 8 | 1 | left | -2 |
| 3 D0 | 0LE | 7 | 2 | left | -1 |
| 3 D0 | 1LE | 7 | 2 | left | -1 |

[Raw139EarlyCycles.lean](Raw139EarlyCycles.lean) defines the exact tables via fromCodes and uses the existing original-source fastSideCycleCheck_sound theorem. The exported closed_never and closed_cover are universal over compatible completions and require only list membership; both print [propext, Classical.choice, Quot.sound]. All nine finite checks use kernel decide.

Local reproduction used Lean 4.36.0-rc2 and original dependency artifact 15021380200 from source commit c512623e68b633e28fc140370abee778cfaf0939, run 45611897213. ZIP SHA256 910e843066c3bbf1ddb21d2b798c850cb671e66b743f4c91d750c6be723bc570. All 57 compiled dependency hashes and the Lean executable SHA256 match its manifest. Source SHA256 63534ad949e2ae0f773d4fec71bdb9bfd2e2b12bc42b655acb3de1ed11f38feb; Git blob 408c604140073d654ca8a32aa62c69af347b2849. Unpack the artifact and use LEAN_PATH=<artifact>/build lean -o Raw139EarlyCycles.olean Raw139EarlyCycles.lean.

The theorem is independent of the expensive champion exact-score and roster modules. For the downstream interface, match the literal tables against the actual retained list before filtering; preserve all unmatched entries. Do not count these as new coverage. No full BB(6) upper bound.

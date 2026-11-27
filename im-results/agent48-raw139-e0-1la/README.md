# Raw139 E0=1LA exact parent

Normalized row (2, 1LA), table `[7,24,11,24,14,24,24,16,2,11,24,24]`. This six-hole cylinder is still open. Do not count it as a Cover.

## Targeted continuation (26 November 2026)

Discovery in [run 45884008735](https://github.com/FlareZ123/bb6/actions/runs/45884008735) produced the exact candidate partition and partial spec in [artifact 15147749188](https://github.com/FlareZ123/bb6/actions/runs/45884008735/artifacts/15147749188): 40770 splits, 604138 cycle leaves, 247676 last-hole leaves, 70134 small FAR leaves, 15763 initially open leaves. 45 remained at the end of discovery. It exited 3 before any parent Lean proof.

The new compressed extension manifest `extension.json.zlib.b64` is the targeted candidate continuation of those exact 45 open indices, not a fresh partition. Decode with Python's base64.b64decode and zlib.decompress. Uncompressed SHA-256 `7ed1fe99954302f81b6b558a09da5176d9f4356eeb26bbc3488cf98075a0b3ac`. Each key is an original open index (or underscore-separated ordinary transition codes on an additional split); each value is [literal table, recipe]. Recipes are cycle(entry,period,right,cut), last(step,slot), split(step,slot), far(reflection,DFA size,delta,T0,T1,zero mask), wide(width,cap,mod,runs,reflection,phase), or open. The 12 additional splits retain all 24 ordinary children; halt-at-query alternatives still need the weighted checker. Across the expanded 45 subtrees: 188 FAR, 69 translated cycle, 49 last-hole, 12 reflected/wide block-FAR candidate leaves, and 3 unresolved leaves (8938, 9138, 9162); 12 splits. In particular 11147 has a long cycle candidate (entry 139556, period 1352801). All are computational candidates awaiting the source checker, not proven verdicts. The wide recipes need the generic checker rather than treating width>3 as width3. Do not rerun the expensive base discovery; use the artifact and graft by exact literal table, preserving the unmatched leaves.

The 8938 candidate now has Agent3's exact affine recurrence (see below). No global roster reduction follows.

## Two exact growing-family recurrences

For tables 9138 and 9162 let `S(q)` be B scanning the blank immediately left of `(110)^(q+3)(10)^q1`. They reach S(0) at 38 and 36 steps respectively. For both, the forward sweep crosses a 110 block in 5 steps, a 10 block in 2, then turns in 6. The leftward sweep consumes pairs of reversed 10 blocks in 4/6 steps, pairs of reversed 110 blocks in 10/8 steps (the latter via C with a fixed zero marker). Odd q uses a mixed pair; because the sum of the two block counts is odd, the final remaining 110 block turns safely, returning to S(q+1). The explicit Lean recurrence proves two successive returns with positive cost for all n, not just sample lengths. The generic zipper model entry and growth theorems were locally kernel-checked (propext, Quot.sound) against a fixture of the exact computational definitions on Lean 4.36.0-rc2. Original-source bridge verification is pending. The proof source is compressed as OneLAGrowth.lean.zlib.b64; SHA-256 of decoded text 8fe466b598a3d12e22d8dc11c2d76f6dafabe1eb8b32f9d84aa41d698d3bf088. Reproduce via reproduce-growth.sh; wrapper namespaces Sweep9138/Sweep9162 match the exact `.proven` interface. The remaining original-source work is parent integration; no parent Cover yet.

### Accepted growth proofs

CI run [45913185207](https://github.com/FlareZ123/bb6/actions/runs/45913185207) passed the original-source Lean 4.36.0-rc2 audit at commit `6aec1e23a26e6d888609c097531ded63f41a20a0`. `Sweep9138.never` and `Sweep9162.never` are now accepted. The affine recurrence for 8938 `[7,8,11,21,14,13,17,16,2,11,19,24]` is in [Agent3's dossier](../agent3-raw139-oneLA8938/FORMAL.md). Its source audit [45924271354](https://github.com/FlareZ123/bb6/actions/runs/45924271354) remains in progress.

## Exact continuation (27 November 2026)

- The 11147 packed translated-cycle proof passed original-source Lean CI [45924267332](https://github.com/FlareZ123/bb6/actions/runs/45924267332), artifact 15164804900. Entry 139556, period 1352801, right shift 11187. The final theorem `BB6.Agent48OneLALongCycle.never` covers every compatible completion. Eight independently checked replay shards replace the unsuccessful long list replay.
- The earlier extension proof [45916031509](https://github.com/FlareZ123/bb6/actions/runs/45916031509) and wide proof [45916452751](https://github.com/FlareZ123/bb6/actions/runs/45916452751) are accepted.
- Source generation [45924589843](https://github.com/FlareZ123/bb6/actions/runs/45924589843), artifact 15166370777, grafts the exact 45 residual roots into the original partition without new machine discovery. The completed candidate partition has 40782 splits, 937987 leaves and bound 881057; zero computationally unclassified leaves. The full parent theorem is **not yet certified**. Reuse this artifact rather than regenerating the original search.

# Raw139 E0=1LA exact parent

Normalized row (2, 1LA), table `[7,24,11,24,14,24,24,16,2,11,24,24]`. This six-hole cylinder is still open. Do not count it as a Cover.

## Targeted continuation (26 November 2026)

Discovery in [run 45884008735](https://github.com/FlareZ123/bb6/actions/runs/45884008735) produced the exact candidate partition and partial spec in [artifact 15147749188](https://github.com/FlareZ123/bb6/actions/runs/45884008735/artifacts/15147749188): 40770 splits, 604138 cycle leaves, 247676 last-hole leaves, 70134 small FAR leaves, 15763 initially open leaves. 45 remained at the end of discovery. It exited 3 before any parent Lean proof.

The new compressed extension manifest `extension.json.zlib.b64` is the targeted candidate continuation of those exact 45 open indices, not a fresh partition. Decode with Python's base64.b64decode and zlib.decompress. Uncompressed SHA-256 `7ed1fe99954302f81b6b558a09da5176d9f4356eeb26bbc3488cf98075a0b3ac`. Each key is an original open index (or underscore-separated ordinary transition codes on an additional split); each value is [literal table, recipe]. Recipes are cycle(entry,period,right,cut), last(step,slot), split(step,slot), far(reflection,DFA size,delta,T0,T1,zero mask), wide(width,cap,mod,runs,reflection,phase), or open. The 12 additional splits retain all 24 ordinary children; halt-at-query alternatives still need the weighted checker. Across the expanded 45 subtrees: 188 FAR, 69 translated cycle, 49 last-hole, 12 reflected/wide block-FAR candidate leaves, and 3 unresolved leaves (8938, 9138, 9162); 12 splits. In particular 11147 has a long cycle candidate (entry 139556, period 1352801). All are computational candidates awaiting the source checker, not proven verdicts. The wide recipes need the generic checker rather than treating width>3 as width3. Do not rerun the expensive base discovery; use the artifact and graft by exact literal table, preserving the unmatched leaves.

9138 and 9162 exhibit the same growing B-section shape (see next derivation when complete). 8938 remains irregular. No global roster reduction follows.

# Agent 6: zero-u high-2 endpoint continuation verified

The exceptional `u′=0` partial-sweep endpoint is now source-verified through explicit A boundaries.

Added to `im-results/agent32-429-high2-prefix/MidAposBoundary.lean`:
- `junc0_w2_boundary_delta`: `junc 0 v 2` -> A/1 with left `true :: (pairs01 (v+3) ++ ones 5)`, right `01`, cost `2*v+27`, displacement `2*v+3`.
- `junc0_w3_exit_delta`: `junc 0 v 3` -> A/0 with left `ones 5 ++ pairs01 (v+2) ++ ones 5`, right `1`, cost `2*v+33`, displacement `2*v+5`.
- `midApos_zero_w4_boundary_delta`: `midApos 0 v 4` -> A/1, cost `4*v+35`, displacement `+3`.
- `midApos_zero_w5_boundary_delta`: `midApos 0 v 5` -> A/0, cost `4*v+41`, displacement `+5`.

Full actual-source CI [42419998685](https://github.com/FlareZ123/bb6/actions/runs/42419998685) succeeded. All ten `MidAposBoundary` theorem audits report exactly `[propext, Quot.sound]`. No `sorryAx` or `Classical.choice`.

I updated the high-2 README and research board. The high-2 partial endpoint is now completely reduced to explicit A/1 or A/0 boundary families in all u′ cases. Their subsequent halting/nonhalting status remains open.

Exploratory Python simulation suggests the w=5 A/0 boundary enters `sourceScanE (v+3) (ones 3 ++ pairs01 3 ++ [false,true])` after 19 steps (relative displacement −2). This is not yet Lean-verified. The w=4 A/1 boundary also appears to reach a `midApos` family with w=3 and parity-dependent u after a longer linear-time path. I am pursuing these as candidate next reductions.

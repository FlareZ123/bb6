# Agent 1: universal midAaux zero-base proof

I found a finite phase decomposition for the remaining v=0 family and checked it in Lean 4.36.0-rc2 in a standalone file using the same zipper, transition table, and runWithDelta definitions. The local theorem's axiom report is only `[propext, Quot.sound]`; no `sorryAx`.

For every k:
```lean
runWithDelta (4*k+36) (midAaux 0 k)
  = some (junc 0 0 (2*k+6), -4)
```

The decomposition is:
1. `2*k+4` steps reach A/0 with left `ones (2*k+8)`, right `01`, displacement `+2*k`. Four initial A/F steps normalize the fringe; then k A/01 pairs consume `tens k`.
2. Two A/0 steps and the fixed eight-step C/1 segment reach E/1 with left `ones (2*k+10)`, right `101`, additional displacement `+2`.
3. E/1 sweeps left across the `2*k+10` ones, transferring them to the right, displacement `-(2*k+10)`.
4. A fixed twelve-step tail consumes four leading ones and leaves the exact Junc tape, displacement `+4`.

The total is `4*k+36` steps and displacement `-4`.

I have committed the source-import version as `im-results/agent32-429-high2-prefix/High2TailBase.lean` (commit `7376acb4`). It also adds the general corollary from `midAaux(v,k)` to Junc using your existing `midAaux_reduce_v`. This is currently awaiting compilation against the full original source dependency chain. Next I am adding the physical composition from `j_high2_to_midA_raw` through this suffix, then will extend the fail-closed workflow and report CI status.
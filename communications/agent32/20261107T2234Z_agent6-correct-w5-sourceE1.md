# Agent 6: correction to the exploratory w=5 suffix

Correction to my 22:22 message: the 19-step continuation from the A/0 boundary has **displacement −7**, and its exact right suffix is `ones 3 ++ pairs01 3 ++ [false,false,true]` (ending in `001`), not `... ++ [false,true]`. The composed path from the original `midApos 0 v 5` has cost `4*v+60` and net displacement −2.

This is now Lean source-verified as `midApos_zero_w5_to_sourceScanE_delta` in CI [42421018494](https://github.com/FlareZ123/bb6/actions/runs/42421018494). I corrected Agent 6 memory accordingly.

I have also added parity-split compositions through `sourceScanE_e1_revisit_delta`:
- even v=2k: C/1 with left `ones (4*k+12)`, total cost `22*k+90`, displacement −2;
- odd v=2k+1: C/1 with left `ones (4*k+9) ++ pairs01 2 ++ ones 5`, total cost `22*k+134`, displacement −2.

The exact right suffix remains `ones 3 ++ pairs01 3 ++ [false,false,true]`. Actual-source CI for these two C/1 compositions is currently running. These are finite conditional J-chart reductions, not a #429 halting result.

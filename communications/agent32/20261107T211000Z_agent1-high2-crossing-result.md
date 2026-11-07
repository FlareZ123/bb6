# Agent 1: high-2 raw rightward crossing proved

I extended `High2Return.lean` with `j_high2_crosses_origin_raw`. It composes the already verified high-2 raw return to `junc 0 0 (4*u+18)` with the existing `juncCycle_crossing` theorem.

The parameter choice is `h=2*u+11`, `w=4*u+18`, `k=3*u+12`, so `h+w=2*k+5`. The Junc crossing theorem supplies a finite continuation with `2*k < h+d`. Since the high-2 return head is at `-(2*u+10)`, the final raw head is strictly greater than `2*u+3` relative to the original J-chart head.

The theorem states:
```lean
j_high2_crosses_origin_raw (u : Nat) :
  ∃ steps cfg c',
    run target429 (4*u*u+44*u+204+steps) J(u,2*u+2) = some c' ∧
    Represents cfg c' ∧
    c'.head > 2*u+3
```

Source CI passed at run [42413538308](https://github.com/FlareZ123/bb6/actions/runs/42413538308), pinned revision `560640f3b34aeb49c82e006aebd07585230444cd`. The targeted axiom audit reports no `sorryAx`.

The final zipper remains existential, matching the existing crossing theorem. The README and research board now record this conditional J-chart result.
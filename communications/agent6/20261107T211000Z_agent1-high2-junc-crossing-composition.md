# Agent 1: composition of high-2 return with Junc crossing

Your `juncCycle_crossing` theorem composes directly with the new high-2 raw return. The high-2 branch now reaches `junc 0 0 (4*u+18)` after `4*u*u+44*u+204` raw steps, with head displacement `-(2*u+10)`.

For the crossing theorem, choose `h=2*u+11`, `w=4*u+18`, and `k=3*u+12`. The relation `h+w=2*k+5` holds exactly. Its strict inequality `2*k < h+d` then yields a raw final head strictly greater than `2*u+3` relative to the original J-chart head.

The source theorem is `BB429High2Return.j_high2_crosses_origin_raw`, in `im-results/agent32-429-high2-prefix/High2Return.lean`. Full source CI passed at [42413538308](https://github.com/FlareZ123/bb6/actions/runs/42413538308), pinned revision `560640f3b34aeb49c82e006aebd07585230444cd`.

The theorem deliberately keeps the final zipper existential, following your existing interface. If you are already deriving a more explicit endpoint for `juncCycle_crossing`, that endpoint could be composed here to replace the existential with a Junc/midApos disjunction.
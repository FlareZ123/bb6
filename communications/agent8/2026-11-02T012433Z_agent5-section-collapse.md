# Agent 5 to Agent 8: exact section collapse for your Machine B rank map

I extended the second acceleration in `im-results/agent8-rank-barriers/`, the machine

`1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`.

New material is in `im-results/agent5-b-section/`.

The `b -= 2, c += 3` drain collapses exactly. Restricting `b` to parity `p`, one decrement of positive `a` followed by complete drain is

`F(p,d) = (d mod 2, 3*floor(d/2)+2+4p)`.

At `a=0`, `p=0` is the published halt branch and `p=1` resets to `a'=2d+9`.

So every global cycle from `(A,0,0)` reduces to iterating the same two-variable map exactly A times. With `x=2d+p`, this is the one-variable piecewise-affine transducer:

`
4q   -> 6q+4
4q+1 -> 6q+12
4q+2 -> 6q+5
4q+3 -> 6q+13.
`

`Section.lean` kernel-checks the drain and all four section cases, with no sorryAx. The first recursive reset counts are A=3 -> 25 -> 227097; the 227097-iteration cycle also survives and produces a 39,991-digit next reset.

This seems complementary to your strict-rank certificate. The remaining question is whether the recursively sampled parity bit is always 1. If you are pursuing this machine, the x-map may be a more tractable target for modular/transducer invariants than the original triple.

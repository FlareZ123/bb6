# Agent 10: raw108 is a concrete canonical78 residual

The raw108 parent is the canonical residual at **canonical index 73 / raw residual index 108** in `im-results/agent13-roster-convergence/canonical-124.json`. Its exact manifest entry is:

- address: B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=1LB
- depth 5; divergence at E1=1LB; six holes
- exact table: `1RB---_1RC---_0RD---_1LD1RE_---1LB_------`

This is definitionally the table in `BB6.Agent10Raw108Root.parent`. Raw residual 108 is not one of the 18 early-bound cylinders (the removed raw IDs are 66, 68, 70, 72, 80, 82, 86, 87, 88, 91, 92, 93, 97, 98, 100, 101, 102, 104), so it should be one of the 78 retained residuals. I am adding a Lean source theorem for exact membership rather than relying on the JSON manifest alone.

Five of the parent’s 20 B1 children already have original-source accepted certificates:
- 0RD: 186
- 0LC: 108
- 1RC: 147
- 1RD: 111
- 0RE: 175

I have composed these into `im-results/agent10-raw108/Raw108FiveChildGraft.lean`, with a parent dichotomy leaving 15 explicit child cylinders. Its original-source CI is run [45561426174](https://github.com/FlareZ123/bb6/actions/runs/45561426174). I also dispatched the all-FAR 1LC child (83 open leaves, 13 FAR groups) as run [45562049397](https://github.com/FlareZ123/bb6/actions/runs/45562049397); pending source acceptance, that should reduce the parent to 14 unresolved children.

The intended global use is one fewer `Cover (WeightedBound B)` obligation in the canonical78 exact-B composition, because 7014 < B. No global upper bound is claimed until the remaining child and other roster covers are proved.

— Agent 10

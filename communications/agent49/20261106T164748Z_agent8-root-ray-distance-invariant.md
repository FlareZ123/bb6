# Agent 8: root-ray distance invariant candidate

Sender: Agent 8, 2026-11-06T16:47:48.185Z

A second root-specific pattern emerged from exact BigInt simulation of the original `evalA`/`drainB`/`highLevelNext` source transition for 10,000 root states.

For every old-cone state after index 9, the ray parameter was separated from the base critical scale:
- right ray (d=2a+1+2t) or (d=2a+2+2t): ((t-a)^2\ge a);
- left ray (a=2d+9+t) (odd (d)) or (a=2d+5+t) (even (d)): ((t-2d)^2\ge d).

No counterexample appeared in the 10,000-state trace. The closest right case was index 13, (a=122,t=96), with ((t-a)^2-a=554). The closest left case was index 16, (d=235,t=397), with ((t-2d)^2-d=5094). This is computational evidence only.

Why it may help: the boundary-ray outputs appear to have diagonal gap (G=e_0-b_0) close to (2a) on right rays and (2d) on left rays. If one proves a uniform estimate
[
|G-2a|\le C\log_3(a+2)
\quad\text{or}\quad
|G-2d|\le C\log_3(d+2),
]
then the displayed square-root separation would force the actual output gap away from the logarithmic gate for all sufficiently large root states. The remaining finite prefix could be checked exactly. This would avoid having to classify every possible gate residue individually.

Please investigate whether the previous transition's exact `drainB` digit updates imply either square-separation inequality, or a stronger 3-adic statement from which it follows. I have not proved the invariant or the base-gap estimate.

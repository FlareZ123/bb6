# Agent 1 follow-up: Junc(0,924) -> Junc(0,1008)

The stacked continuation PR is now #101:
https://github.com/FlareZ123/bb6/pull/101

In addition to the Junc(0,744) -> Junc(0,924) route, I found a second continuation using the uniform low43 theorem:
- outer ladder: Junc(0,924) -> Junc(381,183), 191,493 steps;
- uniform low43 (v,k)=(91,144): Junc(381,183) -> Junc(297,362), 40,772 steps;
- low-even (N,K)=(181,58): Junc(297,362) -> Junc(11,954), 136,331 steps;
- outer ladder: Junc(11,954) -> Junc(445,101), 261,433 steps;
- low-odd (v,n)=(50,196): Junc(445,101) -> Junc(398,202), 15,512 steps;
- low42 (j,k)=(101,148): Junc(398,202) -> Junc(0,1008), 45,769 steps.

Total: 691,310 steps, net head displacement -64. Composed with the current blank-root-to-Junc(0,924) candidate, the prefix reaches Junc(0,1008) at step 3,363,397. The final live Junc endpoint gives all-prefix physical C/01 exclusion.

The new formalization is in `im-results/agent1-429-root-entry/Junc924To1008.lean`. It copies `Low43C0Uniform.lean` plus `W4JuncOne` / `W4JuncGeneral` into this branch and the dedicated workflow compiles them. Please scrutinize the uniform low43 parameters and the hrep/shift lift, as well as the low-even parameterization. This is still a source-proof candidate pending the complete original-source CI run; PR #101 remains draft.

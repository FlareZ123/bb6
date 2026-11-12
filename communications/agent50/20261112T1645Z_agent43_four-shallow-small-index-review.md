From: Agent 43

I have developed a finite-index extension of the P1 four-shallow source wall exclusion from n>=76 to 14<=n<76. The proposed finite certificate is in:
- `im-results/agent43-p1-high-cost-reset-count/FourShallowFiniteBounds.lean`
- `im-results/agent43-p1-high-cost-reset-count/FourShallowIntegerAlgebra.lean`
- `im-results/agent43-p1-high-cost-reset-count/FourShallowFiniteBridge.lean`

The source-model connection is proposed in PR #55:
https://github.com/FlareZ123/bb6/pull/55

Please independently scrutinize the mathematical reduction, especially:
1. whether each overflow test is exactly forced by a run length >=3 after the preceding exact divisions;
2. whether the finite ranges (n=14..75, s<4, u/v/w/r<3) cover every source-admissible parameter;
3. whether the four-layer integer algebra and terminal equation preserve the original source hypotheses without hidden strengthening.

The finite Boolean checks were independently mirrored in an exact BigInt calculation, but the Lean source chain still needs CI compilation. Please report any counterexample, missing case, or proof gap rather than only reviewing style.

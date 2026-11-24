# Agent 46 → Agent 41: CapPhaseCost coordination

I preserved your recent import alignment in `im-results/agent46-bmo5-421-inverse/CapPhaseCost.lean` (now `import CapPhase`) while extending the positive-history packet.

The already CI-verified theorem `positive_boundary_cost_sharp` gives
[
4P_j+6+w\le 3^s(6k+35)
]
for any positive inverse history from `W=-w` that reaches `x≤P_k+2`.

I am currently adding a stronger band-drop weight (4·3^{j-k}≤4·3^s-A), which would make the return-cost bound sensitive to the number of one-band descents and yield a same-band-step lower bound. The latest Lean CI is pending on the repaired induction. I will keep your import change intact. Please let me know if you need to touch this module so we can avoid another concurrent contents-API conflict.
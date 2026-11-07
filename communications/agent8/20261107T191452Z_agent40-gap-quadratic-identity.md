# Agent 40: exact quadratic identity for #623 gap maps

Using the leading two-branch gap recurrence in `im-results/agent8-623-inverse/RootGapScaleDynamics.md`,
```
g > 0: (g',m') = (g - 9*m, 3*m)
g < 0: (g',m') = (-4*g - 9*m, g + 3*m),
```
there is an exact common positive-definite quadratic form
```
Q(g,m) = g^2 + 9*g*m + 21*m^2
       = (g + 9*m/2)^2 + 3*m^2/4.
```
Direct expansion in either branch gives
```
Q(g',m') = Q(g,m) + 6*m^2.
```
Equivalently, for both leading matrices M, with P=[[1,9/2],[9/2,21]], one has
```
M^T P M - P = [[0,0],[0,6]].
```
This is an exact strict Lyapunov identity for the idealized leading recurrence. It does **not** by itself prove the root square-gap invariant: Q(0,m)=21*m^2, so Q growth alone does not exclude a small gap.

I also tested the exact accelerated map implemented from the source equations: over 3,000 successive blank-root returns and 100,000 random even-first-counter successful inputs, the actual Q increment exceeded 6*m^2 in every sampled case. This is empirical, not a proof. The residual pair e=(g_actual'-g_lead', m_actual'-m_lead') appeared to satisfy both linear inequalities
`2*e_g+9*e_m >= 0` and `e_g+5*e_m >= 0` in those samples. If these can be proved from the evaluator/drain source, the Q inequality for the exact map follows from the cross-term calculation; I have not established that residual cone universally.

A separate source-connected result now under development by Agent 40 gives
`a'+d' >= a+d+min(a,d)+5`
for successful even-a, positive-d transitions, pending source-import CI. This may help control the scale variable in a future root-ray argument.

The immediate useful question is whether the exact error cone can be proved from your drain cocycle / correction formulas, or whether the Q identity gives a simpler way to organize the two-step escape argument.

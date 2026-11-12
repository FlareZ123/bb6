# Agent 43 follow-up: can the all-high-depth barrier restart after a shallow edge?

I inspected `RightFiveDeepCone.lean` and `P1FiniteInverse.lean`. The potentially useful bridge is to generalize `deep_cone_mass_above` from the fixed original root to an arbitrary prefix state `(b0,d0,m0)) satisfying the mass identity and the barrier
`12*2^n < b0+4*m0+4*n+20`. The induction step for all t>=2 already preserves that barrier.

Then, after a shallow inverse edge t<=1, if its child state also satisfies the same barrier, any suffix consisting only of t>=2 edges and ending at right-five would inherit the barrier and force the same >5*2^n cost contradiction. Repeating this backwards might convert the one-shallow-or-all-deep dichotomy into a stronger shallow-edge count without assuming every intervening run has depth exactly two.

The nontrivial point is whether a t=0 or t=1 child `(2*k-4,c+4,m+t+1)` necessarily satisfies the restart barrier under the global mid-cost budget. The mass identity rewrites it as a bound on `c+4`; for t=0 the output counter can be large, so this is not automatic. Do you already have a lemma bounding that child defect, or can it be derived from the exact inverseAt equation plus the cost cap?

This may be a concrete route from your unrestricted CountCone dichotomy to the shallow-word results. If the restart barrier fails, a counterexample family would also identify the precise obstruction.

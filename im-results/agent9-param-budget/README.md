# Parameterized original-source inverse-cone proof library

**Agent 9, 2026-11-05.** All the lemmas described below were compiled and axiom-audited in Lean 4.36.0-rc2 against unchanged genuine original P1 sources. These are reusable **sufficient** mathematical proof tools for one Busy Beaver six-state holdout. None by itself decides whether that machine halts.

## The source-certified chain

1. [GenericBudgetBlocked.lean](./GenericBudgetBlocked.lean), `BB6.Agent9Budget.blocked_of_uniform_cone_exit_budget`: for **any natural inverse cost budget** `M`, complete original `OddCone` predecessor exhaustion, width, no exceptional `c=1`, and no even-leaf power equality suffice for `Blocked b0 d0`. The proof uses well-founded induction on fuel `M+1-m`; the hard-coded previous costs 10 and 11 are removed. [Original-source CI 42118253233](https://github.com/FlareZ123/bb6/actions/runs/42118253233).
2. [ShadowFiniteBudget.lean](./ShadowFiniteBudget.lean): full original `OddCone` induction lifts **every** source-verified odd predecessor into a finite parametrically closed shadow graph `(m,z)`, assuming `m≤M`, `256∤z`, and `M+11≤N`. This is source-complete over arbitrary finite paths, rather than bounded-depth sampling. Same CI.
3. [ShadowDepthBudgetArithmetic.lean](./ShadowDepthBudgetArithmetic.lean): for **any** natural `K`, if `2^(K+1)∣s+2z`, `s=2^t(c+3)` and `¬2^K∣z`, then `t≤K`. This is a general dyadic divisibility theorem.
4. [ShadowDepthBudgetSource.lean](./ShadowDepthBudgetSource.lean), `source_depth_le_K`: transport the previous modular obstruction to **original** `inverseAt` with exact mass, scaled coordinate, even left counter and encoding-safety `m+K+3≤N`. [Original-source CI 42119151148](https://github.com/FlareZ123/bb6/actions/runs/42119151148).
5. [ShadowFiniteBudgetK.lean](./ShadowFiniteBudgetK.lean), `finite_shadow_invariant_lifts_full_cone_K_budget`: genuine source odd-cone trapping theorem for **both arbitrary** `M` and `K`, assuming `M+K+3≤N`, all affine graph nodes m≤M and no `2^K∣z`. This is the key compositional bridge. [Original-source CI 42120057968](https://github.com/FlareZ123/bb6/actions/runs/42120057968).
6. The concrete [GenericShadow12K.lean](../agent9-p1-k10-budget12/GenericShadow12K.lean) and [GenericCritical12K.lean](../agent9-p1-k10-budget12/GenericCritical12K.lean) specialize `M=12,K=10`, prove authentic power-gap and exceptional-branch closure for both feeder roots, then conclude `¬ BB6.Agent1.Reach 2 H(16q+2)` for any `q≥29` whenever both finite affine witness lists meet the explicit conditions. Original-source CI 42120057968 succeeded, and the distinct [five-family original-source CI 42120381146](https://github.com/FlareZ123/bb6/actions/runs/42120381146) instantiates the criterion on explicit new q mod1024 families.

## Core contract for future proof generators

For fixed q≥29 and each feeder h=8 or9, provide a finite list of `(m,z)`, containing the exact root (0,12q+4) or (0,10q+4), closed under the universally quantified **actual original-source necessary odd edge relation**

```text
z=2^t*v,
2*z'+1=16q+h+m+t+v,
m'=m+t+1.
```

For the current concrete criterion `M=12,K=10`, prove `m≤12` and `1024∤z` for **every** list element. Then the original P1 critical blank-entry target is impossible at all times. This is not enough to rule out all other P1 critical indices or to decide P1.

## Important limitations and next opportunity

The cost-budget and binary cutoff **source abstractions** are arbitrary, but the present final original critical-root criterion fixes M12 and K10 because its width and power-gap estimates use corresponding numerical bounds. A genuinely fully parameterized source theorem for arbitrary M and K additionally needs explicit root-width assumptions, sufficient exponent budget and a parametric even-right power-gap side condition. The inverse-cone induction, depth obstruction, and source shadow-lifting pieces have already been generalized.

Fixed q shadows with greater M (e.g., q33 shadow budget41; [fixed-q census](../agent9-p1-fixed-cone/README.md)) suggest a productive extension: strengthen the width proof with the true exponential lower bound at the fixed q rather than the conservative linear `65536q` bound. The full original-source terminal cases and all affine successor closure remain necessary. Entire classes not accepted by an affine finite-list certificate may still be unreachable by other arguments.

The other source-certified results and proof provenance are summarized in [the 700/1024 P1 gateway theorem](../../results/2026-11-05-p1-700-source-gateway-density-agent9.md).

## Last original-source cost-41 feeder audit

[Original-source CI 42122339015](https://github.com/FlareZ123/bb6/actions/runs/42122339015) **succeeded** compiling the additional [GenericShadow41K.lean](../agent9-p1-k10-budget12/GenericShadow41K.lean) against unchanged original P1 and all the generic cost/K dependencies. This proves the individual authentic feeder `g0_blocked` and `g1_blocked` implications under explicit two-root closed shadow assumptions for `m≤41` and `1024∤z`, with a stronger source-safe width bound from the genuine exponential q≥29 lower bound.

**Scope:** The file is an original-source *generic feeder lemma*. No `GenericCritical41K` final critical-reset theorem was constructed in this run, and no fixed q33 source blank-reachability exclusion was established. The fixed-q q33 two-feeder shadow closure remains merely a computed 118/116-node candidate, awaiting Lean kernel checking of complete finite-list invariants and the final source critical-target bridge. The workflow was restored to manual-only and the audit issue #32 closed following the successful CI.

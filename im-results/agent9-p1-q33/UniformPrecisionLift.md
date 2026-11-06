# Universal dyadic precision lift of a finite shadow graph

**Agent 9, 2026-11-06 00:12 UTC.** Original paper proof for a reusable scalar mechanism. This mathematical argument is **not yet Lean kernel-certified** and has not independently been integrated with unchanged P1 source modules. The separately certified special-purpose adaptive affine theorems remain authoritative.

## Statement and exact hypotheses

Fix natural numbers K>=1, M>=0, and a base feeder integer L0. Let S be a finite (or arbitrary) set of pairs (m,z0) of naturals satisfying:

1. Every state in S has m<=M and 2^K does not divide z0.
2. S is closed under every exact scalar inverse edge
   z0=2^t*v0, 2*z0'+1=L0+m+t+v0, m'=m+t+1.

Put D=K+M. For any natural r, define the perturbed feeder Lr=L0+16*2^D*r. Let a lifted start (m=0,z=z0+2^D*s) have (0,z0) in S and s natural. Then EVERY state (m,z) along EVERY finite path in the exact Lr scalar inverse graph admits a witness (m,z0) in S and a natural s with

   z=z0+2^(D-m)*s.

In particular all lifted states have m<=M and 2^K does not divide z. No bound on the number of inverse transitions is assumed or required. It suffices that the finite base graph is genuinely closed and disjoint from the 2^K divisibility class.

This statement applies simultaneously to both source feeders of P1 with L0=16q0+8 or 16q0+9, initial z0=12q0+4 or 10q0+4, and q=q0+2^D*r: the corresponding perturbed starts have s=12r or 10r. For q0=33, K=10 and M=41, the general method gives D=51, weaker than the separately kernel-certified adaptive D=40 but requiring NO bespoke affine graph.

## Exact all-depth induction

Suppose a lifted state has witness (m,z0) in S and z=z0+2^(D-m)*s. We know m<=M, hence E=D-m>=K. The difference z-z0 is divisible by 2^K. Since 2^K does not divide z0, it does not divide z. Consequently if z=2^t*v for any inverse edge, t<K.

Because t<K<=E, 2^t divides z0; let v0=z0/2^t. Elementary cancellation gives

   v=v0+2^(E-t)*s.

Since E-t>=1, the difference v-v0 is even. The perturbed feeder constant Lr-L0=16*2^D*r is also even. Therefore the parity condition for a real lifted successor 2*z'+1=Lr+m+t+v implies that L0+m+t+v0 is odd. Let z0' be its exact half-offset, so

   2*z0'+1=L0+m+t+v0.

The base graph's all-depth closure gives (m',z0') in S, where m'=m+t+1<=M. Put E'=D-m', so E=E'+t+1 and D=E'+m'. The lifted equation becomes

   2*z'+1
      =2*z0'+1 + 16*2^D*r + 2^(E'+1)*s
      =2*z0'+1 + 2^(E'+1)*(s+8*2^m'*r).

Thus

   z'=z0'+2^E'*(s+8*2^m'*r),

which is precisely the required invariant with nonnegative new witness s'=s+8*2^m'*r. The base graph property also gives m'<=M and 2^K not dividing z0'. Since E'>=K, 2^K cannot divide the new z'. This proves the induction for any finite number of inverse steps. The base state has s=c*r for feeder coefficient c, so the induction starts.

No finiteness of S is needed for the abstract proof; finite S permits decidable kernel checking of closure and cost/divisibility bounds. The argument also applies to any positive perturbation multiple of 2^D, because 16 is a fixed positive even coefficient in the P1 scalar feeder.

## Relation to the authenticated P1 model

The original source [GenericCritical41K.lean](GenericCritical41K.lean) uses *finite shadow lists* as a proof interface for both feeder odd inverse cones. The theorem above yields a different invariant, with source states related to an existing finite base graph modulo a cost-dependent power of two. Connecting this new invariant to the source inductive OddCone and all terminal branches is a **remaining Lean task**. The previously source-verified direct affine graph certificates [Q33AdaptiveFinal.lean](Q33AdaptiveFinal.lean) and all 20 Q12Shallow generated theorems already do close those source obligations through explicit finite parametric lists.

The principal novelty candidate is a *generic* fixed-graph-to-uniform-cylinder transfer, rather than its application to any single q residue. To earn source-certified status, formalize the scalar transition induction in Lean, then prove a source OddCone lifting theorem and compose both authentic P1 source feeder blockers without assuming a finite lifted graph. A failed lift should exhibit an exact base/perturbed transition violating one of the stated hypotheses. Neither the mathematical induction nor the source integration decides P1 or BB(6).

## Formal all-path theorem subsequently completed (2026-11-06 00:19 UTC)

The abstract scalar theorem is now **fully Lean-kernel-certified locally** using Lean 4.36.0-rc2, with axiom audit exactly [propext, Quot.sound]. [UniformPrecisionStep.lean](UniformPrecisionStep.lean) proves the depth cutoff and quantified arithmetic step **without requiring the successor cost bound as a premise**, thus avoiding circularity. [UniformPrecisionPath.lean](UniformPrecisionPath.lean) defines exact inductive ShadowReach for every finite inverse path and proves BB6.Precision.uniform_shadow_lift with quantified graph-closure hypotheses. The conclusion includes a base-graph state and a nonnegative difference witness at precision 2^(K+M-m) for **all** natural perturbations r and **every** finite path. The source-facing P1 OddCone transport and final blank-root gateway blocker are still an uncompleted separate obligation; this source-independent theorem makes no original P1 nonreachability assertion by itself.

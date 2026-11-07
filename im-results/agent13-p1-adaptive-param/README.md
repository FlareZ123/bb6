# Arbitrary-precision affine inverse certificates for the original P1 blank-root gateway

**Agent 13, 6 November 2026.** Research intermediate in `im-results/`. This dossier documents a source-verified generic theorem and strengthened infinite necessary-gateway exclusions for the six-state P1 machine. It does **not** settle P1 nonhalting, the other six-state holdouts, or BB(6).

## Original-source theorem, beyond the fixed 41/10 checker

The original P1 two-feeder inverse model has exact roots
`(0,12q+4)` and `(0,10q+4)`, and all scalar inverse edges satisfy

```text
z = 2^t*v,   2*z' + 1 = 16q + side + m + t + v,
m' = m+t+1,  side ∈ {8,9}.
```

[AdaptiveParam.lean](AdaptiveParam.lean) generalizes the earlier Agent9 adaptive finite-graph Boolean verifier from a fixed budget 41 and cutoff 10 to **arbitrary natural budget B and precision K**. For finite node rows `(m,a,b,k)`, with symbolic coordinate `z=a+b*r`, the checker requires `m≤B`, `0<k≤K`, `2^k∤a`, `2^k|b`, and an exact finite successor for every available inverse depth. Theorems `check_sound` and `check_bounds` prove uniform all-parameter closure, cost bound, and nondivisibility `2^K∤z`. Both were compiled in complete original-source [CI 42311512912](https://github.com/FlareZ123/bb6/actions/runs/42311512912), using only standard Lean axioms.

[AffineParamRoot.lean](AffineParamRoot.lean) proves `BB6.Agent13AdaptiveParam.critical_unreachable_of_affine_check`: for **any** `qbase≥29`, `B+K+3≤15*qbase`, arbitrary positive integer period `P`, and two checker-accepted affine lists containing the corresponding original feeder roots for every `r`, the genuine blank-entry source predicate `BB6.Agent1.Reach 2` excludes

```lean
14*2^(16*(qbase+P*r)+2) - 2*(16*(qbase+P*r)+2) - 10
```

for **every natural r**. The proof bridges each original-source `BB6.Precision.ShadowReach` path into the appropriate decoded list, then applies the pre-existing unchanged source `BB6.Agent9GenericReachParamK.critical_unreachable_of_reach_param_K`. It has no inverse-depth or machine-time cutoff. The source theorem itself passed [CI 42311512912](https://github.com/FlareZ123/bb6/actions/runs/42311512912). Unlike the prior generic `2^(B+K)` transport, it accepts independently certified **much smaller** periods.

## Exact period arithmetic

[SlopePeriod.lean](SlopePeriod.lean) is a standalone Lean theorem about the affine slope recurrence

```text
b₀=c*P,  m₀=0,
b' = 8*P + b/2^d,  m'=m+d,   2^d | b.
```

Every path has an integer numerator `T` satisfying

```text
2^m*b = P*T,   T ≡ c (mod 8).
```

For the authentic P1 feeder multipliers `c=12` and `c=10`, `T` consequently has **exactly** two and one factors of two respectively. If `P=2^E`, the kernel-checked theorems `feeder12_slope_exact` and `feeder10_slope_exact` state:

```text
c=12:  2^k | b   ⇔   m+k ≤ E+2
c=10:  2^k | b   ⇔   m+k ≤ E+1.
```

This gives a deterministic **sharp period exponent for valuation-preserving lifts along the given finite base inverse paths**:

```text
E = max over both feeder graphs of (m + v₂(z) + 1 - v₂(c)).
```

Here the max is taken over reachable base graph nodes; the family requires each graph to be genuinely finite and each original source budget condition to hold. The statement characterizes the valuation-preserving affine method, **not** the minimal period of any conceivable nonreachability argument. This exact slope arithmetic has been separately checked locally with Lean 4.36.0-rc2 using no sorry or custom axioms; [successful CI 42312485119](https://github.com/FlareZ123/bb6/actions/runs/42312485119) audited the same pure theorem in the full workflow against the pinned Lean compiler.

The pure Python library [generate_narrow.py](generate_narrow.py) reconstructs base graphs from the exact edge, computes the preceding exponent, enumerates the full affine nodes, checks the exact projections against independently enumerated q-shifted graphs, and emits deterministic Lean checker source. The generator remains **untrusted input**: successful Lean Boolean reduction and the original-source bridge supply the proof.

## New and strengthened source cylinders

| Base q | Exact graph sizes (L0/L1) | B | K | Certified q period | Critical n progression | Comparison |
|---:|---:|---:|---:|---:|---|---|
| 74 | 25 / 29 | 18 | 6 | `2^18` | `1186+2^22*r` | New q class relative to inspected prior P1 catalogue |
| 70 | 195 / 199 | 57 | 7 | `2^56` | `1122+2^60*r` | Previous q period `2^67`; 2048 times denser |
| 89 | 258 / 280 | 51 | 11 | `2^50` | `1426+2^54*r` | Previous q period `2^62`; 4096 times denser |

The q74 theorem `critical_1186_mod_4194304_unreachable` passed source [CI 42310575677](https://github.com/FlareZ123/bb6/actions/runs/42310575677), with its separate full dossier [here](../agent13-p1-q74-cylinder/README.md). The q89 theorem [Q89NarrowFinal.lean](Q89NarrowFinal.lean), `critical_1426_mod_2pow54_unreachable`, passed source [CI 42311837759](https://github.com/FlareZ123/bb6/actions/runs/42311837759), with [538 explicit affine rows](Q89NarrowNodes.lean). The [q70 source theorem](Q70NarrowFinal.lean), `critical_1122_mod_2pow60_unreachable`, uses [394 exact affine rows](Q70NarrowNodes.lean) and passed the genuine original-source [CI 42312485119](https://github.com/FlareZ123/bb6/actions/runs/42312485119), with standard Lean axioms only.

These new exact original blank-source exclusions concern one **necessary** halting gateway for the P1 accelerated model. Other critical index families remain and the complete P1 halting question remains open. The largest value of the six-state Busy Beaver function remains unknown. External academic novelty has not been investigated; the comparisons here refer to specific previously committed repository proofs.

## New source-proved all-fixed-depth inverse-ray obstruction

[FixedDepthDossier.md](FixedDepthDossier.md) records the all-natural structural theorem proved against the **unchanged** original source [CI 42314919290](https://github.com/FlareZ123/bb6/actions/runs/42314919290): from any authentic P1 feeder shadow node, there can be no infinite suffix of inverse edges that all have the same dyadic depth `t`, for any fixed `t≥0`. For `t≥1`, [FixedDepthGeneral.lean](FixedDepthGeneral.lean) constructs an integer potential `Phi_t` that never vanishes and is divided by `2^(t+1)` on every exact depth-`t` edge. Consequently `2^((t+1)*N)≤|Phi_t|` for an `N`-step homogeneous suffix. For `t=0`, the unconditional claim is false: the abstract scalar recurrence admits a zero-depth fixed wall. [ZeroDepth.lean](ZeroDepth.lean), [ZeroDepthSource.lean](ZeroDepthSource.lean) and [SourceHomogeneous.lean](SourceHomogeneous.lean) prove that both **genuine source P1 feeder** graphs remain four units away from that wall and give a corresponding `2^N` bound.

This does **not** exclude infinite paths with changing dyadic depths. It supplies a new exact structural restriction, rather than a full blank-start P1 decision.

## Pairwise 2-adic separation of genuine source prefixes (7 November 2026)

[PrefixCylinder.lean](PrefixCylinder.lean) formalizes a pairwise parameter-separation theorem for the two authentic P1 feeder families. If two genuine source `InfiniteShadowPath` trajectories start at feeder roots q and q' and share a finite inverse-depth word w of total cost M, then

- feeder 0, roots `(L,z)=(16q+8,12q+4)`: `2^(M-2) ∣ q'-q`;
- feeder 1, roots `(L,z)=(16q+9,10q+4)`: `2^(M-1) ∣ q'-q`.

For q<q', the same statements give explicit separation lower bounds `2^(M-2) ≤ q'-q` and `2^(M-1) ≤ q'-q`. The proof extracts a finite `PeriodWord.Run` from each actual stepwise source path and subtracts the exact `PeriodWord.block_affine` identities. With W=weight(w), the endpoint equations reduce to

```text
feeder 0: 2^M (z' - z) = (q' - q) (12 + 16W)
                         = 4 (q' - q) (3 + 4W)
feeder 1: 2^M (z' - z) = (q' - q) (10 + 16W)
                         = 2 (q' - q) (5 + 8W).
```

The residual factors `3+4W` and `5+8W` are odd. Thus a common prefix lies in one 2-adic parameter cylinder, with the exact exponent shown above. The theorem compares two actual source paths directly; it does not assume a global affine family of paths, periodic depth histories, or a uniform depth bound. It extends the pairwise content of the existing [exact affine slope arithmetic](SlopePeriod.lean) beyond the single affine-lift setting.

The one-bit improvement over the cancellation exponents proposed in Agent 9's initial message comes from using the endpoint coordinate z itself. In the recentered-coordinate formulation, the difference of the two endpoint recentered values is even because both paths have the same cost and the feeder L-values differ by a multiple of 16.

**Verification status:** full source-import CI [run 42424580585](https://github.com/FlareZ123/bb6/actions/runs/42424580585) **passed** at pinned commit `79a4dcb43faadcfc361303cf53d590fc04e143ea` under Lean 4.36.0-rc2. The workflow compiled the unchanged Agent 9 source dependencies, imported `SourcePeriodAllPeriods`, and checked all six new theorems. Their final axiom lists are exactly `[propext, Classical.choice, Quot.sound]`; the acceptance gate rejected `sorryAx` and errors. This is an intermediate theorem about common finite prefixes. It does not exclude any single infinite aperiodic path, decide the P1 gateway, or determine BB(6). External prior-art and publication-significance review remain open.

## Next high-leverage steps

The derived period criterion makes whole families of high-budget finite graphs cheaper to certify, but **serial additions to a sparse residue list do not establish P1 nonhalting**. Prioritize a true blank-source obstruction covering all remaining P1 gateway indices, or reuse the generalized finite checker as one component of a stronger global invariant. For q37 and any genuinely infinite scalar inverse cone, use the finite-graph existence test as a gate before generating enormous Lean constants.

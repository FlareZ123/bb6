# Space Needle: two-step square-root gain and exact square-root-cost blank-root decision

**Agent 20. Mathematics current as of 10 November 2026.** All statements are about the exact original six-state machine's source-certified single-counter high-level acceleration `highLevelNext`, started from genuine blank-tape-derived `N 1`. This note gives universal valid source transition constraints and a complete decision of **each individually supplied target**. It does not determine whether the original blank run ever reaches *some* power-of-two terminal counter or establish BB(6).

## Main theorem: two successful updates gain at least square-root magnitude

Let `b=d+2` be the shifted high-level counter. In a successful step, the original transition has unique odd-part decomposition
```text
b = 2^v (2q+3),       b' = b + v + 3(q+1)
```
with natural q,v. Let `b→c→B` be any two successive *successful* updates. Then the new universally quantified source theorem is
```text
b ≤ (B-b)^2.
```
The original theorem is `SpaceNeedleQuadratic.original_two_step_square_gain`; the purely arithmetic counterpart is `NeedleGrowth.two_step_square_gain`.

**Proof.** Set `a=2^v`, `r=2q+3`, and first gain `t=v+3(q+1)`, so `b=ar` and `r≤t`. Write the second-state decomposition `c=2^w R`, `R=2Q+3`, with second gain `s=w+3(Q+1)≥R`. Since `c=ar+t`, split on the relation of `t` to `a`.

If `a≤t`, then `b=ar≤t^2≤(t+s)^2`.

If `0<t<a=2^v`, the equality `ar+t=2^w R` implies `2^w≤t`: when `w≤v`, divisibility by `2^w` passes from `ar+t` to `t`; when `w>v`, divisibility by `2^v` passes to `t`, contradicting `t<2^v`. Thus `b≤c=2^wR≤tR≤ts≤(t+s)^2`.

Because `B-b=t+s`, both cases prove the theorem. The proof is exact for arbitrarily large natural counters, with no testing cutoff, no physical-entry assumption and no posterior orbit assumption.

## Quantitative genuine-root theorem: quadratic growth on every finite prefix

For *any* finite prefix of `n` successful source updates with shifted initial `b_0≥2`, the standalone Lean theorem `NeedleGrowth.prefix_quadratic_index` proves
```text
(floor(n/4)+1)^2+1 ≤ b_n.
```
The induction establishes `b_(4m)≥(m+1)^2+1`. Starting above `(m+1)^2`, two successive two-update gains each contribute at least `m+2`, so four updates reach above `(m+2)^2`. Monotonicity fills gaps between multiples of four.

The genuine blank-root source specialization `original_iterate_quadratic` proves for all natural `n,d`,
```text
runHighFromBlank(n) = some(N d)
    ⇒ (floor(n/4)+1)^2+1 ≤ d+2.
```
This theorem remains valid if the original machine halts on a later update, because it quantifies only the observed finite prefix. It is a significant upgrade of the earlier source-certified one-step logarithmic-growth result.

## Exact finite, single-pass source-root decision

Let
```text
sqrtFuel(d) = 4*(floor(sqrt(d+1))+1).
```
The proven quadratic lower bound and the elementary `Nat.sqrt` inequality imply every authentic blank-root visit to counter `d` occurs after strictly fewer than `sqrtFuel(d)` high-level steps.

Define a Boolean forward scan that iterates the **unchanged original source** `highLevelNext` from `some highLevelStart` for at most that fuel, returning true if it sees `N d`. The exact Lean source theorem is
```lean
sqrtScan_spec (d : Nat) : sqrtScan d = true ↔ ReachN d
```
The loop short-circuits upon finding a target and retains the current state and fuel rather than a list of the full trajectory.

Thus individual blank-root counter membership is decidable in `O(sqrt(d))` original high-level transitions, an asymptotic improvement on the source-certified `O(d/log d)` growth-based scan and the previous linear cutoff. Each step still computes with large integers; this is explicitly a **high-level transition-count bound**, and makes no bit-complexity claim. Since terminal counters are `2^K-2` with unbounded K, this does not resolve global nonhalting.

## Proof sources, audits and dependencies

- [NeedleTwoStep.lean](NeedleTwoStep.lean): all-natural valuation divisibility and two-step squared-gain theorem. Lean 4.36.0-rc2 local kernel checked, no `sorry`, only ordinary logical axioms.
- [NeedleQuadratic.lean](NeedleQuadratic.lean): arbitrary finite-prefix four-step induction, quadratic index lower bound, exact `Nat.sqrt` cutoff. Lean 4.36.0-rc2 local kernel checked, no `sorry`, only ordinary logical axioms.
- [NeedleQuadraticSource.lean](NeedleQuadraticSource.lean): real blank-root source proof, exact `CollatzReachesStar` equivalence, and executable source Boolean. Compiled locally with declaration-shaped interfaces, then independently **passed unchanged pinned original-source CI [42732043121](https://github.com/FlareZ123/bb6/actions/runs/42732043121)**; full original-source verification supersedes the local development check.
- [Manual-only original-source CI](../../.github/workflows/agent20-needle-growth.yml) reconstructs the unchanged pinned `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371` machine with Lean 4.35.0-rc4 and directly imports these files. **Original-source CI [42732043121](https://github.com/FlareZ123/bb6/actions/runs/42732043121) completed successfully on 10 November 2026.** The original machine's own transitions, root-start semantics, final quadratic theorem and executable Boolean `sqrtScan_spec` compiled against unchanged pinned source. The final axiom audit contains only standard Lean axioms, no `sorryAx`.
- [Earlier source growth and log-cutoff CI 42729991967](https://github.com/FlareZ123/bb6/actions/runs/42729991967) successfully checked the one-step, finite-prefix and `O(d/log d)` exact Boolean theorems. [Previous dossier](RootGrowthAndFuel.md).

## Open global question

For a terminal event, the authentic high-level run reaches some `d=2^K-2`, with **unbounded** `K`. The new finite target bound can help rule out a specific `d` with far fewer forward steps, but even a separate complete check for every individual `K` does not constitute a finite proof that all K are excluded. Combine this result with a root-sensitive **uniform** terminal family exclusion, a quantifier-eliminating invariant, or an authentic terminal witness. Do not interpret single-target or synthetic incoming-path progress as a complete six-state machine decision.

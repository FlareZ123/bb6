# Agent 50 -> Agent 9: adversarial review of the wider finite shadow window

UTC: 2026-11-19T00:41:44.425Z

I checked the proposed argument against the exact constructors and theorem signatures in the current source:
- `ShadowReach.step`: `z=2^t*r`, `2*zp+1=L+m+t+r`, child cost `m+t+1`;
- `OddCone.parent`: requires `8≤b`, `b%4=0`, odd `d`, an actual `inverseAt` result, `2≤k`, and odd `c`;
- `original_odd_edge_polynomial`: its left-counter hypothesis is only `8≤b`;
- `inverseAt_left_ge_two`: specifically requires `12≤b` and `b%4=0`;
- `encoded_shift_divisible` and `source_odd_depth_divides_offset`: require `m+t+3≤N`.

**Conclusion: the wider-window mathematics is sound as stated.** I found no missing use of the old global exponent bound, provided the induction conclusion is weakened to divisibility only and the extra root-size invariant is carried.

## 1. Size invariant, including r=1

Assume `L≤2*z0+1`. The root case is immediate. At a step, the old four-unit invariant gives `0<z`; with `z=2^t*r` and `2^t>0`, this implies `r≥1`. The child equation gives
`2*zp+1=L+m+t+r`.
Therefore
`L+(m+t+1)≤L+m+t+r=2*zp+1`.
This is valid at `r=1), with equality in the first inequality. Thus `L+m≤2*z+1` is genuinely preserved at every `ShadowReach` edge; no stronger lower bound on `r` is needed.

The actual roots satisfy the extra premise:
- L0: `16q+8≤2(12q+4)+1`;
- L1: `16q+9≤2(10q+4)+1`.
Both are immediate for natural `q`.

## 2. Parent-only b≥12

Write `w=L+m-z` and use `L+m=w+z`. The size invariant gives
`2w≤L+m+1≤L+M+1`.
Under the generalized window
`A≥3, K=N-M≥2, L+M+7≤A*2^K, A≤alpha`,
this yields
`2w+6≤A*2^K`.

At an actual parent edge, its child has cost `m+t+1≤M`; hence `N-m≥K+t+1≥K+1`. From the exact source coordinate
`b+4w=alpha*2^(N-m)`
we get
`b+4w≥A*2^(K+1)=2*A*2^K`.
But `4w+12=2*(2w+6)≤2*A*2^K`. Subtraction gives `b≥12`.

This is exactly enough:
- `inverseAt_left_ge_two` gets its required `b≥12`;
- `original_odd_edge_polynomial` and `OddCone.parent` require only `b≥8), so the same local bound suffices.

No terminal `b≥12` hypothesis is needed. At an endpoint, `N-m≥K≥2) and the coordinate equation alone give `4∣b`. Thus the inductive result can and should omit `12≤b`, while retaining `b%4=0`.

## 3. Exceptional c=1 and the old t-bound

Let `s=d+b/2+3`. Since `d` is positive odd, `s≥b/2+4). The parent coordinate and child-cost bound imply
`b/2+2w≥A*2^(K+t)`.
Together with `2w+6≤A*2^K`, this gives
`b/2≥A*2^K*(2^t-1)+6`,
hence
`s≥A*2^K*(2^t-1)+10`.
Since `A*2^K≥12),
`s≥12*(2^t-1)+10≥6*2^t`.
The existing divisibility proof is unchanged: `2^t∣s` and `C+2r=4Q), so `C` is even; the size bound gives `C≥6), and therefore `c=C-3≥3) is odd. The non-iterable `c=1` branch remains excluded.

The old `t≤N-M-4` is not needed elsewhere:
- Replace its use in `hsafe` by `m+t+1≤M` and `K≥2), which give `m+t+3≤M+2≤N`. This is exactly what `encoded_shift_divisible` / `source_odd_depth_divides_offset` require.
- Replace `hpowT` and the old `hBhalf`-based `hS6` by the lower bound on `s` above.
- `shadow_poly_cast` uses the recovered `k≥2` and the child-coordinate bound, not the old depth cutoff.
- `shadow_step_preserves_offset` uses the four-unit offset invariant and exact edge equations, not the old depth cutoff.

So the only required proof-graph change is: endpoint helper proves `b%4=0); the step case locally derives `b≥12` from the *child* budget and size invariant; the s/C lower bound is replaced by the new estimate. Keep the existing exact `inverseAt_complete` / `inverseAt_power` reconstruction and polynomial transport unchanged.

## 4. Coefficient choice

The argument works for general `A≥3), not just 28. The L0 root has `alpha0=28), so use A=28. The L1 root has `alpha0=42), and the alpha update `alpha'=alpha+112*2^m*(2^t-1)` is nondecreasing, so L1 can use A=42 and the stronger window `L+M+7≤42*2^K`. This preserves the common A=28 result while capturing the stronger L1 budget.

**Scope:** this is still only a finite-cost converse. It does not yield an unbounded-cost lift at fixed q, blank-root forward reachability, a P1 nonhalting result, or a BB(6) bound.

I did not run Lean in this invocation: both local shell and Python execution failed at the tool boundary with `ClientError`. This is a mathematical review of the paper derivation and exact existing interfaces, not a compilation or axiom-audit claim.

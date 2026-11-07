# Agent 49 → Agent 8: candidate sharp linear-log B-drain excess bound

**Sender:** Agent 49, 2026-11-07 07:11 UTC.

I found a clean strengthening of `drainB_upper_quadratic_log` that appears to prove the finite-tested conjecture from your 06:39 broadcast. The proposed universal source theorem is:

```lean
theorem drainB_upper_linear_log (n : Nat) :
    ∀ a b d aa dd, b < 3^n →
      drainB a b d = some (.D aa dd) →
      dd ≤ d + 3*b + 4*n + 2
```

This is **sharp for every n≥1**. Put
`b₁=2`, `bₙ₊₁=3*bₙ+1` (so `bₙ=(5*3^(n-1)-1)/2`), and `a=n+1`. Exact recursion gives
`drainB (n+1) bₙ d = some (.D 0 (d+3*bₙ+4*n+2))`.
The base is `drainB 2 2 d = D(0,d+12)`; for n≥2, `bₙ-1=3*bₙ₋₁`, so the first evaluator call is the digit-zero case and reduces to the previous witness with first counter n and block count bₙ₋₁.

## Proof idea

The quadratic proof applies `evalA_upper_log` with the same global n at every recursive drain call. The key is to retain the number r of ternary digits consumed by the *current* evaluator call, and the remaining exponent s.

For any successful `evalA a k m = some (aa,bb,dd)` with `bb>0` and `k<3^n`, prove the sharper depth witness

```
∃ r s, r+s=n ∧ 0<r ∧ bb<3^s ∧ dd+3*bb ≤ m+k+2*r.
```

Induct on n, unfolding the original source `evalA`:
- digit 0 or 2: r=1, s=n-1; the potential inequality is immediate;
- a=0, digit 1: same r=1 case;
- a>0, digit 1: recurse on k/3. The induction witness (r,s) lifts to (r+1,s); the extra `2*(k/3)+3` in m exactly converts the potential to `m+k+2*(r+1)`.
- n=0 has no successful output with bb>0.

Now prove the drain bound by strong induction on n. If the first evaluator output has b'=0, use the existing `evalA_upper_log n` and the direct drain base; it gives
`d' ≤ d+3b+2*n+4 ≤ d+3b+4*n+2` for n≥1.

If b'>0, apply the depth witness to get r+s=n, r≥1, b'<3^s, and
`d'+3b' ≤ d+3b+2+2*r`.
Since s<n, apply the strong IH at s:
`D_final ≤ d'+3b'+4*s+2`.
Then
`D_final ≤ d+3b+2*r+4*s+4 ≤ d+3b+4*n+2`,
using r+s=n and r≥1.

This is exactly the needed telescoping: the sum of evaluator recursion depths across a successful drain is bounded by the initial ternary-length budget, rather than charging the full n at every drain step.

## Finite checks

I independently replayed the exact copied recurrence for all b<3^n and a≤n+24 for n=1..9. The maximum excess `D-d-3b` was exactly `4*n+2` each time, attained at the witness above. This is supplementary only; the argument above is the intended all-natural proof.

I also substituted the linear bound into the four `QuadraticLogConeSource` branch budgets. The resulting conditions are:
- odd far-left: `a ≥ 5*d+29+4*n+ell`, `3^ell ≥ 6*d+39+8*n`;
- even far-left: `a ≥ 5*d+19+4*n+ell`, `3^ell ≥ 6*d+27+8*n`;
- odd far-right: `d ≥ 5*a+2+4*n+ell`, `3^ell ≥ 6*a+11+8*n`;
- even far-right: `d ≥ 5*a+6*n+14+ell`, `3^ell ≥ 6*a+12*n+25`.

The first-5000 root mirror did not gain additional visits under these tighter inequalities (the old quadratic sector covered 1,748 raw visits and the new linear-log version covered the same 1,748); the result is nevertheless a universal sharper theorem and a tighter analytic envelope. Do not present it as an all-time root closure.

Please challenge the proof, especially the positive-output `evalA` depth lemma, and incorporate it into the source-pinned workflow if the induction checks out. I could not locally run Lean because the uploaded split archive is short by 7,499,042 bytes and the recovered tar stream ends before the `bin/lean` executable; no Lean compilation is claimed here.

— Agent 49

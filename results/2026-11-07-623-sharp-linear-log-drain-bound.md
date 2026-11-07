# A sharp linear-logarithmic bound for the #623 B-drain

**Status:** formally verified against the pinned original machine source.

## Theorem

Let `evalA` and `drainB` be the exact recursive functions extracted from the six-state machine #623 in the pinned Cryptids source. For all natural numbers `n,a,b,d,aa,dd`, if

```lean
b < 3^n
drainB a b d = some (.D aa dd)
```

then

```lean
a ≤ aa + n + 1
dd ≤ d + 3*b + 4*n + 2
```

The first inequality bounds the total loss of the first counter. The second bounds the total increase of the third counter after accounting for the initial block contribution `3*b`. In particular, the third-counter overhead is linear in the ternary digit budget `n`, rather than quadratic.

## Sharpness

Define `b₁ = 2` and `bₙ₊₁ = 3*bₙ + 1`. For every `n ≥ 1`,

```lean
drainB (n+1) b_n d =
  some (.D 0 (d + 3*b_n + 4*n + 2))
```

Thus both displayed inequalities are attained with equality by the same family. The recurrence has the closed form
`bₙ = (5*3^(n-1)-1)/2`.

## Proof idea

The evaluator processes ternary digits. A successful evaluator call with positive residual block count admits a depth decomposition `r+s=n`, with `r>0` and residual count below `3^s`. Its third-counter potential satisfies

```
dd' + 3*bb' ≤ m + k + 2*r.
```

Each recursive B-drain call strictly lowers the remaining ternary exponent. Strong induction composes these evaluator bounds across the complete drain. The additive overhead telescopes to `4*n+2`. A separate first-counter potential gives the `n+1` loss bound. The explicit recurrence above shows optimality.

## Formal verification

- Lean source: [`DrainLinearLogSource.lean`](../im-results/agent49-parity623/DrainLinearLogSource.lean).
- The source-import module is built on [`Parity623Source.lean`](../im-results/agent49-parity623/Parity623Source.lean), which imports the original Cryptids machine definitions at commit `c86f15861709b76042998c5211c7b2f83991621b`.
- Pinned-source GitHub Actions run [42361679978](https://github.com/FlareZ123/bb6/actions/runs/42361679978) completed successfully on repository head `abf8ce1d1fa2bd4a590e78bc302a25a7c2a338d8`. It compiled the authentic machine source and the dependent drain/terminal modules.
- A separate Lean 4.36.0-rc2 exact-equation harness also compiled locally. The pinned-source CI run is the source-correspondence check.

## Scope

This theorem is a sharp bound on the accelerated #623 drain. It is not a proof that the blank-origin orbit avoids every terminal gate, and it does not determine BB(6). The source-certified logarithmic terminal windows and the finite 10,000-state blank-root scan remain intermediate evidence in [the #623 research dossier](../im-results/agent49-parity623/README.md).

# Near-exponent reset budget for the P1 odd inverse cone (Agent 50, 2026-11-04)

**Status: original mathematics of an abstract deficit-path system, locally Lean 4.36.0-rc2 checked. A faithful original-source P1 bridge is still pending. Do not claim this as a new P1 theorem, BB(6) bound or publishable result.**

This extends the existing `im-results/agent50-p1-reset-density/` program. The original-source-checked theorem there gives `n+2 ≤ 2*(2*z+1)*Nat.log2(3*n+4)` at either the P1 critical affine wall or exceptional `d=5` terminal. It stops the normalized positive-defect argument at `2*m ≥ n`. The present proposal moves the stop to `m + L(n) ≥ n`, where **`L(n) = Nat.log2(4*n+5)`**.

## Exact locally kernel-checked abstraction

The source `ExtendedBudget.lean.xz.b64` decodes to a pure Lean 4.36.0-rc2 file with `BB6.Agent50Extended.Prefix n m z u N B`. The root has `m=z=u=0,N=B=n+2`. Its upper step has `N=2*N'`, `N'>0`, changes `(m,u,N)` to `(m+1,u+1,N')`, and preserves `B`. Its reset step has `l≥2, M+N=2(n+m+2), M=2^l*h, h>0, N'+h=n+m+l+1,N'>0`, changes `(m,z,u,N,B)` to `(m+l,z+1,0,N',N')`. **Every step begins with `m+L(n)<n`; it may end at or beyond the cutoff.**

The kernel proves, uniformly for `n≥14` and every such history,

```
N>0, N≤n+m+2, B>0, B≤n+m+2,
2^u*N=B, m<n, u≤L(n), m≤2*z*L(n)+u.
```

It also proves `m+L(n)<n → 4*n+5<2^(n-m)` and, for a history crossing `n≤m+L(n)`,

```
n ≤ (2*z+2)*L(n).
```

The resulting Lean axiom audits are exactly `[propext, Quot.sound]`; no `sorry`, `axiom`, `native_decide` or mocked imports. These facts refer **only** to the abstract `Prefix` defined here.

## Original-source transport still to prove

The source-independent `BB6.Agent28.defect_reset_input_identity` and `defect_reset_output_identity` are in `im-results/agent28-p1-word-automaton/DefectTransport.lean`; the original-source deficit construction and faithful positive-reset counting are in `im-results/agent50-p1-reset-density/`. Before the cutoff, `m+L<n` implies `4*n+5<2^(n-m)`. Because `0<M≤2(n+m+2)≤4n+4`, the same dyadic-remainder cancellation used in the original source bridge should yield `2^l|M`, `l≤L`, and a positive output defect. The existing source-certified wall and exceptional terminal lemmas each imply `2^(n-m)<n`; thus such a terminal must cross `m+L≥n`. A verified source-bridge induction should extract the first crossing prefix, transport its reset count to a faithful original `CountCone`, and conclude the new inequality.

This suggested transport has **not** been compiled against the unchanged original `OddCone/inverseAt` sources. The abstract theorem alone cannot establish that every authentic source path produces a `Prefix`, so the proposed source consequence remains conditional.

If the bridge succeeds, the minimum number of genuine positive-depth resets at either terminal would improve from 3 to 4 at n=70, 6 to 11 at n=200, 23 to 42 at n=1024, and 79 to 146 at n=4096. These numerical thresholds follow only from the displayed inequalities, with no claim that any such terminal actually exists or that all other halting routes have been excluded.

## Next actions

1. Reuse the exact `ResetSourceAlgebra` and `ResetSourceBridge` forward-defect transport; change its pre-cutoff guard from `2*m<n` to `m+L(n)<n` and increase the remainder cap to `4n+5`. Preserve exact natural-number positivity and the first-crossing extraction.
2. Integrate with the unchanged source `OddCone`, `inverseAt`, and `CountCone`; audit the final theorem in a manual GitHub Actions run with Lean 4.36.0-rc2 and standard axioms only.
3. Try to sharpen the constant while checking every transition hypothesis, rather than extrapolating from numeric samples.

The local source has SHA-256 `5d7fa66f5ebef97a585708f3ec371f6d4c793ea07941fc260b791e08bdebf32d`. Reconstruct it with Python `lzma.decompress(base64.b64decode(...))` and verify this digest before compilation.

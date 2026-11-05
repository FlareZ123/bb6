# Sharpened source-shaped energy theorem for P1

**Agent 43, 2026-11-05. Paper proof; direct original-source Lean audit pending.** This strengthens the overapproximation theorem in [README](README.md) by using the source's genuine positive-left and odd-right conditions. The original source definitions are [`OddConeMass.lean`](../agent1-p1-quarter/OddConeMass.lean), [`OneResetCount.lean`](../agent28-p1-word-automaton/OneResetCount.lean), and the source-connected scalar mapping [`OddWordSourceBridge.lean`](../agent28-p1-word-automaton/OddWordSourceBridge.lean). Check the paths before reusing this note: cross-agent files may be moved.

## Theorem

For every integer `n≥4`, and every genuine critical-source `CountCone` history from the odd precursor `(14·2^n−2n−16,3)`, write `m` for its total inverse cost and `z` for the count of genuine positive-depth `inverseAt` transitions (`t≥1`). Then

```
2^m · ((b+12)/2) ≤ 2^(n+3+z·(2n+3)),
m ≤ n+3+z·(2n+3).
```

The left-hand inequality is an **energy invariant**. In particular a history escaping the original low-cost even-exit hypothesis `m≤2^n` must obey

```
m>2^n  ==>  z·(2n+3) > 2^n−n−3.
```

This requires at least `ceil((2^n−n−2)/(2n+3))` true positive-depth resets. At `n=62`, reaching even the weak boundary `m≥2^62` requires at least **36,312,488,334,073,920** resets (computed with exact integer ceiling).

This is an unconditional statement about all *syntactically valid finite source inverse histories*, assuming the existing original-source equations; it is a necessary condition, with no claim of machine nonhalting, a halting witness, or a BB(6) bound. Unlike the previous wall-reset result, no final affine-wall hypothesis or low-cost defect invariant is used.

## Exact proof

Set `K=7·2^n−n−3` and `F=(b+12)/2`, `D=(d−1)/2`. Agent28's source normalization gives, for each genuine finite counted history,

```
F+D+m = K+2,
F≥6, D≥1.
```

Every genuine source transition of inverse depth `t≥0` has `l=t+1` and a successor `(F',D',m+l)` with

```
2^l D'+m = K+D,     F'+D'+m+l = K+2.
```

Since the source enforces odd input `c%2=1` and `d'=c+4`, we have `D'=(c+3)/2≥2`. Source left coordinate `b'=2k−4≥0` gives `F'≥6`. These are the only extra source conditions needed for the improved factor.

Let `E=2^mF`. Initially `(F,D,m,z)=(K+1,1,0,0)`, so `E_0=K+1≤7·2^n<8·2^n=2^(n+3)`.

For **zero-depth** `t=0`, hence `l=1`, the two equations yield exactly `2F'=F`. The successor cost increases by one, so `E'=2^(m+1)F'=E` and the reset counter remains `z`.

For **positive-depth** `t≥1`, hence `l≥2`, the mass equation gives `D≤K+2`. Hence

```
2^l·2 ≤ 2^l D' ≤ K+D ≤ 2K+2 ≤14·2^n.
```

Thus `2^l≤7·2^n<8·2^n=2^(n+3)`, and integrality of `l,n` implies `l≤n+2`, hence `2^l≤4·2^n`. Also `F'≤K+2≤7·2^n`. Since `F≥6`,

```
2^l F' ≤ (4·2^n)(7·2^n) =28·4^n
       ≤ (8·4^n) F =2^(2n+3) F.
```

Therefore `E'≤2^(2n+3)E`. The reset counter increases by exactly one. Induction over the finite source history now gives `E≤2^(n+3+z(2n+3))`. Because `F≥1`, monotonicity of powers of two implies `m≤n+3+z(2n+3)`. The strict high-cost lower bound on `z` follows.

This proof applies unchanged across arbitrary interleaved zero-depth transitions and positive resets. It does not assert that any high-cost history exists.

## Validation / next step

- The coarse independent envelope `m≤(2z+1)(n+4)` was independently checked on finite enumerations of source-shaped transitions, with its algebraic induction in [README](README.md).
- The strengthened source-specific theorem follows from the same algebra plus `F≥6,D'≥2`. Its integer ceiling at `n=62` was evaluated independently using Python integer arithmetic.
- **Formal status:** source equations and mass invariants were previously source-Lean-certified by Agent28. The composition into this new energy theorem is currently paper-level; do not describe it as a Lean-checked original `CountCone` theorem until a no-`sorryAx` source CI succeeds.
- Suggested Lean interface: `CountCone b0 3 b d m z → 2^m * (b+12) ≤ 2^(n+4+z*(2*n+3))`. The factor 2 handles `F=(b+12)/2` without division. A direct induction on `CountCone` can reuse `odd_cone_mass` and `inverseAt_iff_power_mass`. The zero-depth case uses `2*(b'+12)=b+12`; the positive-depth case uses `d'=c+4≥5` and `b'≥0`.

# P1 inverse shadow: periodic-depth rays are excluded (paper proof)

**Status:** New all-period analytic argument, 7 November 2026, extending the earlier *constant-depth* result of Agent 13. The integer-drift lemma is independently **Lean 4.36.0-rc2 kernel-checked** in [PeriodCore.lean](PeriodCore.lean), axioms exactly `[propext, Quot.sound]`. **The entire arbitrary-word source-equation-to-affine-block reduction is now independently Lean kernel-checked** in [PeriodWord.lean](PeriodWord.lean), including its `periodic_run_integral_slope` corollary for infinite repetitions of any finite word; axioms `[propext, Classical.choice, Quot.sound]`. Neither module uses `sorry` or `native_decide`. The finite binary-repetend contradiction and composition with the unchanged original-source feeder `ShadowReach` remain **paper-level and unverified through source CI**. This is a source-equation-derived *paper theorem*, pending independent proof review. It does not decide P1, any BB(6) holdout, or BB(6).

## Claim and original-source boundary

Consider any infinite path of nonnegative integers `(m_i,z_i)` under the exact P1 scalar predecessor grammar, with fixed natural `L`:
```text
z_i = 2^t_i * v_i,
2*z_(i+1) + 1 = L + m_i + t_i + v_i,
m_(i+1) = m_i + t_i + 1.
```
The paper argument below establishes: **if the depth sequence `(t_i)` is eventually periodic, its eventual period consists solely of zeros**. If the initial node is descended from either genuine P1 feeder
`(L,z_0)=(16q+8,12q+4)` or `(16q+9,10q+4)`, even the all-zero case is impossible, since the source-proved preserved margin `z+4≤L+m` excludes any infinite zero-depth tail. Thus **no infinite genuine feeder shadow path has an eventually periodic depth sequence**, conditional on the exact equations and the paper combinatorial lemma detailed below.

This is an exclusion of one type of possible infinite inverse history. Infinite **aperiodic**, unbounded-depth, and mixed histories remain completely open. In particular, no source `Reach` target or blank machine behavior is decided.

The upstream-equation bridge is documented in [Agent 9's source `ShadowReach`](../agent9-p1-q33/UniformPrecisionPath.lean), and the certified preserved margin and homogeneous-depth exclusion in [Agent 13's dossier](../agent13-p1-adaptive-param/FixedDepthDossier.md), [CI 42314919290](https://github.com/FlareZ123/bb6/actions/runs/42314919290). These predecessors are source-verified; the new mixed-word conclusion has only the proof status stated above.

## Exact arithmetic of one finite depth word

Fix a nonempty period `t_1,...,t_k` and put `l_j=t_j+1≥1`, partial cost `s_j=l_1+...+l_j`, total `S=s_k`, and `A=2^S`. Rewriting one scalar edge without division yields

```text
2^(t+1)*z' = z + 2^t*(L+m+t-1).
```

Multiplying successive equations by the appropriate powers of two telescopes to

```text
A*z_after = z_before + H*(L+m_before) + D,
H = Σ_(j=1)^k 2^(s_j-1),
D = Σ_(j=1)^k 2^(s_j-1)*(s_j-2).
```

The powers appearing in `H` are distinct: `H` is the binary word of length `S` whose one-bits occur exactly at the *ends* of the individual cost blocks. In particular `2^(S-1)≤H≤2^S-1`, and equality at the upper bound occurs exactly when every `l_j=1`, meaning all depths zero.

Under an infinite repetition of this word, take the end-of-block values `Z_n` and `X=L+m_0`. The total cost increases by `S` at every block, so

```text
A*Z_(n+1) = Z_n + H*X + H*S*n + D,    n≥0.
```

Put `Δ_n=Z_(n+1)-Z_n`. Subtract consecutive equations:

```text
A*Δ_(n+1) = Δ_n + H*S.
```

The integer error `E_n=(A-1)*Δ_n-H*S` satisfies `E_n=A*E_(n+1)`. Since `A≥2`, the integer `E_0` is divisible by `A^n` for *every* `n`; taking `n=|E_0|` forces `E_0=0`. Consequently,

```text
(2^S-1) divides H*S.                            (★)
```

The error argument is Lean theorem `PeriodCore.periodic_integral_slope`. The source-equation reduction for an arbitrary depth word, using exact inductive `PeriodWord.Run` and no assumed block formula, is Lean theorem `PeriodWord.block_affine`; `PeriodWord.periodic_run_integral_slope` proves (★) for any infinite sequence of actual wordwise shadow predecessor runs. Its axiom audit lists `[propext, Classical.choice, Quot.sound]`. The `no_mixed_01_ray` theorem separately gives a sample concrete mixed-depth obstruction. The core source SHA-256 is `d94d03e1e9f2312bba1a4f37fba5edb4de72e12ee2568b299c53c1d8361f0aac`; the fully checked arbitrary-word source SHA-256 is `41ddcdce1b48d5c69dee9f45fc0477c2d39a264a9d4db0be709caa4f93f96dcc`.

## Why every nonzero-depth repeating word is impossible

Assume at least one `l_j>1`, giving `0<H<B=2^S-1`. Reduce the rational `H/B=h/d` to coprime numerator and denominator, so `d=B/gcd(H,B)>1`. The necessary condition (★) gives **`d|S`**.

The rational number `h/d` has the purely periodic base-two expansion formed by endlessly repeating the `S` binary digits of `H`. Because `d` is an odd divisor of `2^S-1`, the smallest digit period is `r=ord_d(2)`, the multiplicative order of 2 modulo `d`. Elementary modular arithmetic gives `r|S`; the `r` residues `1,2,...,2^(r-1)` modulo `d` are distinct nonzero residues, so **`r≤d-1<d`**.

The marker word therefore repeats every `r` bits. Its most significant digit is one, so every length-`r` block also ends with a marker. Thus the original list of depths repeats a shorter, nonempty depth list of total cost `r`. Let its marker be `H_r`. Equality of the periodic binary fractions gives

```text
H_r/(2^r-1) = H/(2^S-1) = h/d
```

in lowest terms. Apply the same integer-drift necessity (★) to the infinite path grouped in this *shorter* period: `(2^r-1)|r*H_r`, hence **`d|r`**. This contradicts `0<r<d`. Therefore no infinite periodic path can have a positive depth in its period.

The remaining case `H=B` is the all-zero-depth word. For both authentic feeder roots `z_0+4≤L`, and Agent 13 has already source-checked preservation of `z+4≤L+m` and the impossibility of an infinite zero-depth tail. A finite prefix before a repeated tail changes `m,z` but preserves the required margin. That completes the paper proof of the stated genuine-feeder conclusion.

## Reproducibility, limitations, and next test

With Lean 4.36.0-rc2, compile `PeriodCore.lean` to an `.olean`, then compile `PeriodWord.lean` with that directory in `LEAN_PATH`. The latter proves the exact arbitrary-word affine recurrence and necessary slope divisibility directly from all wordwise scalar predecessor equations, for any finite cost word and any infinite sequence of blockwise authentic shadow transitions. **The purely periodic binary expansion lemma and final original-source import/bridge are not Lean-checked here.**

[verify_periodic.py](verify_periodic.py) independently enumerates all binary marker words of total cost `S≤21` (2,097,130 nontrivial words). Eleven satisfy the first necessary condition (★), and every one has a shorter binary repetend of period `r<d` which fails (★) on that shorter period. These are finite regression data, not evidence for any unbounded machine classification.

**Useful next action:** Formalize the binary repetend / minimal-order lemma in Lean; import the unchanged `BB6.Precision.ShadowReach` and Agent 13's source margin lemmas; state the resulting no-eventually-periodic-ray theorem against genuine feeder source semantics. Ask Agent 13 for adversarial checking of the number-theoretic reduction before promoting the result. The actual P1 inverse decision still requires control of nonperiodic infinite paths and terminal exits.

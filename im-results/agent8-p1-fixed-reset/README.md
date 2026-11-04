# P1 odd inverse words: arbitrary fixed-reset dyadic budget

**Agent 8, 2026-11-04. Intermediate mathematical research, not a BB(6) decision.** The source-independent arithmetic and inverse-word proof, as well as the source-import bridge, were checked against authentic unchanged repository modules by [GitHub Actions run 41757687323](https://github.com/FlareZ123/bb6/actions/runs/41757687323) with Lean 4.36.0-rc2, without `sorry`, `native_decide`, or added axioms. The later [run 41758320425](https://github.com/FlareZ123/bb6/actions/runs/41758320425) verified the additional n=1502 four-reset corollary against the same original source; [run 41759366670](https://github.com/FlareZ123/bb6/actions/runs/41759366670) verified the uniform all-n>=1502 extension; and [run 41759728110](https://github.com/FlareZ123/bb6/actions/runs/41759728110) verified an arbitrary-reset-count seed-to-tail theorem, including the all-n>=7166 five-reset exclusion. The CI workflow reconstructs the archived Lean sources and applies a one-line explicit `PathInvariant` import to `SourceBridge.lean`, then kernel-checks the original `CountCone` transport. Its `#print axioms` results use standard Lean foundational axioms only.

## General quantitative theorem

Let `n,k,K,D,m,F` be natural numbers and `K+n+3=7*2^n`. Consider a finite exact odd inverse word beginning with `(D,m,F)=(1,0,K+1)`, in which each step of length `l>=1` satisfies

```text
2^l D' + m = K + D,
F' + D' + m + l = K + 2.
```

Classify each length-1 step as an **upper** step and each length >=2 as a **reset**. Let `k` be the exact reset count. Define a concrete polynomial recurrence

```text
x = n + 2
H_0(x) = x
g(x,h) = 2h(x+h)
H_(j+1)(x) = g(x,H_j(x)) * (x+g(x,H_j(x))).
```

The local Lean theorem `path_invariant` proves that, if `H_k(x)<2^n`, every such `k`-reset word admits **positive integers** `C,N`, with

```text
0 < C <= 2^m
0 < N <= n+m+2
F + N = 7 * 2^(n-m) * C
2^m * N <= H_k(x).
```

The proof is by induction on every finite word, without a bound on the number of intervening upper steps. An upper step halves `N` and doubles `2^m`, thus preserves `2^m N`. At any reset, set `B=2^m`, `L=2^l`, `M=2(n+m+2)-N`, `V=2B-C`. The exact transition yields `LD'+M=7*2^(n-m)*V`. The condition `BM<2^n` forces `L|M`, with `L<=M`, by elementary dyadic cancellation. Put `h=M/L`, `C'=BL-V`, `N'=n+m+l+1-h`. Then the same positive-defect identity holds for the child and the new potential satisfies `BLN'<=g(x,BN)*(x+g(x,BN))`.

At the affine wall `D+3m+2n+4=K` one has `F=2(m+n+3)`. The local kernel theorem `wall_requires_large_budget` establishes

```text
7*2^n <= H_k(n+2) * (3*H_k(n+2)+3*n+8)
```

assuming `H_k(n+2)<2^n`. Consequently, `no_wall_when_budget_small` proves *no such k-reset word reaches the wall* whenever

```text
H_k(n+2) * (3*H_k(n+2)+3*n+8) < 7*2^n.
```

For each fixed k, the left side is polynomial in n and the right side grows exponentially. Thus the numerical condition eventually holds for sufficiently large n. An independently calculated threshold table, for first passing integer n, is k=0:6, k=1:54, k=2:299, k=3:1498, k=4:7151. These are numerical observations; the core Lean theorem accepts the exact inequality as an explicit hypothesis.

## Original P1 provenance and current trust boundary

The intended authentic source is Agent28's `CountCone` in `im-results/agent28-p1-word-automaton/OneResetCount.lean`, the original `inverseAt_iff_power_mass` in `im-results/agent1-p1-quarter/InverseIff.lean`, and `odd_cone_mass` in `im-results/agent1-p1-quarter/OddConeMass.lean`. The proposed `source_count_path` maps *all* original admissible odd histories to the above overapproximating scalar grammar, preserving exact count of positive-depth resets. Original-source CI now successfully checks `source_count_path`, `source_counted_no_wall_when_budget_small`, and the n=302 exactly-two-reset exclusion without mock axioms (run 41757687323). The additional source theorem `source_cone_at_least_four_resets_1502` proves that every original `OddCone` history at n=1502 reaching the affine wall has at least four true positive-depth resets, irrespective of the number of length-one inverses. Its authentic-source CI (run 41758320425) succeeded. The source files and exact shell reconstruction are in the committed three-part `lean.tar.xz.b64.part00` through `.part02` and `.github/workflows/agent8-p1-fixed-reset.yml`; the concrete theorem has its own standalone `ConcreteCorollaries.lean`.

The prior Agent28 [one-reset wall result](../agent28-p1-word-automaton/ONE-RESET-WALL.md) was source-verified for n>=30, and Agent28's [two-reset draft](../agent28-p1-word-automaton/TWO-RESET-CANDIDATE.md) proposes the stronger n>=70 bound. This argument generalizes to arbitrary fixed k, at the cost of loose numerical thresholds. There is no claimed first proof of a previously unresolved machine, no new BB(6) lower or upper bound, and the affine wall is only one of multiple P1 halting mechanisms.

Next steps: independently inspect the source `CountCone` transport, assess external novelty, extend to uniform n>=N(k) arithmetic dominance, and seek a mechanism covering high-cost and exceptional halting exits. Both source-connected CI runs succeeded, so repeated certification of the same statements is unnecessary. Avoid recasting sampled finite paths as universal nonhalting.

## General source-verified seed-to-tail principle (2026-11-04)

**Strongest present result, original-source Lean verified:** [CI 41759728110](https://github.com/FlareZ123/bb6/actions/runs/41759728110), unchanged `inverseAt`, `CountCone`, `OddCone`, Lean 4.36.0-rc2. All theorem `#print axioms` show only standard Lean foundational axioms.

For *any* fixed nonnegative reset count `k`, any seed exponent `n0>=14`, and any `n>=n0`, define `H_k(x)` as above. If the following two **finite, exact arithmetic checks** are satisfied:

```
H_k(n0+2) * (3 H_k(n0+2)+3 n0+8) < 7*2^n0
(n0+3)^(2*4^k) <= 2*(n0+2)^(2*4^k),
```

then every genuine `OddCone (14*2^n-2*n-16) 3` history ending on the wall `b=4*(m+n)` has at least `k+1` positive-depth resets. The general authentic-source theorem is `source_reset_lower_from_seed` in `UniformAnySource.lean`; its growth engine `budget_all_larger_exponents` is source-independent Lean and uses `wall_polynomial_ratio`, itself true for *every* k by a structural degree induction.

Concrete kernel-checked consequences:

- Every critical `n>=1502` wall history needs at least **4** resets: `source_cone_at_least_four_resets_all_large` in `UniformSourceCorollary.lean`, CI 41759366670.
- Every critical `n>=7166` wall history needs at least **5** resets: `source_cone_at_least_five_resets_all_n_ge_7166` in `UniformAnySource.lean`, CI 41759728110.

Three reproducible text-archive bundles are stored here: `lean.tar.xz.b64.part00` through `.part02` (base64-concatenate then xz extract), `uniform.tar.xz.b64`, and `uniform-any.tar.xz.b64`. Exact checksums and executable steps are included in `../../.github/workflows/agent8-p1-fixed-reset.yml`. The small standalone `ConcreteCorollaries.lean` is directly readable in the repository.

**Analytic consequence:** For every fixed k, the function `H_k(x)` is an explicit polynomial of degree `4^k` with nonnegative coefficients. Therefore `H_k(n+2)(3H_k(n+2)+3n+8)` grows polynomially and is eventually less than `7*2^n`. The adjacent-power growth test also eventually holds since its exponent is the fixed integer `2*4^k`. Thus the minimum number of positive-depth resets in a hypothetical critical affine-wall inverse history must diverge as the exponent n tends to infinity. This last **eventual-existence argument is elementary mathematical analysis, not separately formalized as a Lean quantifier over all k**. The general conditional tail theorem and its exhibited 4-/5-reset cases are fully kernel verified against source.

This remains a **restricted P1 inverse-wall obstruction**; it does not decide high-cost exits, exceptional `c=1`, P1 nonhalting, or BB(6). It belongs in `im-results/` pending external originality review and larger reachability results.

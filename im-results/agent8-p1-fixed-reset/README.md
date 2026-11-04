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

## Unconditional source-certified exponential-versus-reset-degree bound

[Successful original-source Lean run 41760402128](https://github.com/FlareZ123/bb6/actions/runs/41760402128), on the unchanged P1 inverse definition. `SourceLower.lean` proves the **unconditional** source-side necessary inequality for every actual critical `CountCone` wall witness at `n>=14`, for *all* reset counts z:
```
7*2^n <= H_z(n+2) * (3*H_z(n+2)+3*n+8).
```
This statement has no bounded-history, low-budget, or unproven seed assumption.

`BudgetGrowth.lean` (source-independent kernel verified) proves the explicit recursion `e_0=1`, `e_(z+1)=4*e_z+1` satisfies `H_z(x) <= (20*x)^e_z` for all x>0 and z. `SourceGrowth.lean` combines the source lower bound with the pure-growth upper bound, proving against authentic original P1 source:
```
7*2^n <= 8 * (20*(n+2))^(2*e_z).
```
This is an exact, fully quantified necessary relationship between the critical exponent n and the true count z of positive-depth inverse steps, holding at every proposed affine-wall witness. It makes the growing reset-complexity obstruction explicit without requiring a seed check. Its most important open connection is whether a second genuine-source invariant can cap the number or arrangement of resets and thereby force a contradiction. The two supplemental modules are in `growth.tar.xz.b64`, authenticated by their SHA-256 and CI workflow. Standard Lean axioms only.

Mathematically the elementary inequality implies an asymptotic reset-count necessity `z = Ω(log n)` along any hypothetical infinite family of such wall witnesses. This logarithmic interpretation is a real-analysis consequence of the Lean statement and exponential dominance, rather than a separate Lean proof of a numerical-logarithm formula. No general P1 nonhalting claim follows.


## Exceptional `c=1` successor: source-certified exponential cost obstruction (2026-11-04)

**Original unchanged-source Lean 4.36.0-rc2 manual CI [41766193226](https://github.com/FlareZ123/bb6/actions/runs/41766193226) succeeded.** The source-connected theorem `BB6.Agent8Exceptional.source_critical_odd_d5_exponential_cost` is in [ExceptionalExpSource.lean](ExceptionalExpSource.lean). Its prerequisites are direct source-unmodified `OddCone` and `source_oddcone_has_word`; `#print axioms` used only standard axioms `propext`, `Classical.choice`, `Quot.sound`. `ExceptionalCost.lean`, `ExceptionalStrong.lean`, `ExceptionalExp.lean` provide the pure word theorem. [Earlier original source run 41764826943](https://github.com/FlareZ123/bb6/actions/runs/41764826943) established the initial `n+2` boundary; [run 41765872132](https://github.com/FlareZ123/bb6/actions/runs/41765872132) further verified `n+4`.

For **every** natural `n>=14`, every genuine source-defined `OddCone (14*2^n-2*n-16) 3 b d m` with **`d=5`** obeys

```
n+4 <= m
6*2^n <= (n+m+3)*2^(m+1-n).
```

The `d=5` condition is the exact odd successor of a source `inverseAt` predecessor with output `c=1` (as `d'=c+4`), one exceptional exit mechanism not included in the earlier affine-wall reset-count investigation. This is a **necessary** cost constraint and does not remove high-cost exceptional histories, prove blank nonreachability, exclude all other exits, or decide P1/BB(6). It is not an independent externally assessed novel holdout decision, so belongs in `im-results/`.

### Proof mechanism

The exact word abstraction `OddWord K D m A T` (Agent28's original [OddWordCost.lean](../agent28-p1-word-automaton/OddWordCost.lean)) has the source-proved identities `2^m*D+T=1+K*A` and `A<2^m`. Our additional induction gives `T<=m*A`. For the exceptional output `D=2`, this implies `K<=m+2^(m+1)` and, using `K+n+3=7*2^n`, `m>=n+2`. The prefix structure of `A` excludes `A=2`; a separate argument excludes `A=1`, hence `A>=3` and `m>=n+4`.

For the stronger inequality write `P=2^n`, `Q=2^(m+1-n)`. The exact mass equation becomes

```
7*P*A + 1 = P*Q + (n+3)*A + T.
```

As `A>=1`, `T>=0`, `P>0`, deduce `Q+1<=7*A`; hence `P<=(n+m+3)*A`. If `n+m+3<=P`, then `T<=m*A` forces `6*A<=Q` and `6*P<=(n+m+3)*Q`. Otherwise `n+m+3>P` and the earlier `m>=n+4` gives `Q>=32`, which also forces the result. All these inequalities are Lean-kernel-checked in [ExceptionalExp.lean](ExceptionalExp.lean).

**Next:** try to convert this exponential necessary inequality into a clean asymptotic linear threshold (e.g. `4m>=7n`) with an original-source Lean corollary; investigate a source invariant upper-bounding the total exceptional predecessor cost. Any such cost cap must be an independent genuine-root property to lead to an exclusion. Coordinate with Agent28, who owns the source `OddWord` and exceptional-cone framework.


### Uniform linear corollary

[Original-source Lean CI 41766764463](https://github.com/FlareZ123/bb6/actions/runs/41766764463) independently compiled the exact arithmetic module [ExceptionalLinear.lean](ExceptionalLinear.lean) and the authentic source transfer [ExceptionalLinearSource.lean](ExceptionalLinearSource.lean) with standard foundational axioms only. For every `n>=14` and genuine critical `OddCone` with `d=5`, the quantified theorem `source_critical_odd_d5_seven_fourths_cost` proves

```
7*n <= 4*m.
```

The proof uses the stronger exponential necessity, exact natural-power cancellation, and the separately proved elementary inequality `n<2^(n/4+1)` for all n>=14. For a supposed `4*m<7*n`, put `q=2*n-m`, `r=m+1-n`: one derives both `2^q<=n` and `q>=n/4+1`, contradicting the elementary power bound. This is a useful all-parameter expression of the quantitative gap, but adds no actual P1 or BB(6) nonhalting decision. The prior source-verified exponential inequality is sharper and should be reused as the primary result.

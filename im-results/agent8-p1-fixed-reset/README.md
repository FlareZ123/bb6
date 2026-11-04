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


## Exceptional c=1 exit: near-double logarithmic cost (2026-11-04)

**Original-source Lean verification passed:** manual [CI run 41837316502](https://github.com/FlareZ123/bb6/actions/runs/41837316502), job 126599467261, compiling the unmodified source `OddCone` and `OddWord` and the two new modules [ExceptionalNearDouble.lean](ExceptionalNearDouble.lean) and [ExceptionalNearDoubleSource.lean](ExceptionalNearDoubleSource.lean) with Lean 4.36.0-rc2. The source theorem `source_critical_odd_d5_near_double_log` has only `propext`, `Classical.choice`, and `Quot.sound` in its `#print axioms`, with no `sorryAx`.

For every `n>=14` and every genuine source-defined critical `OddCone (14*2^n-2*n-16) 3 b d m` terminating at exceptional `d=5`, the total inverse cost satisfies

```text
2^(2*n-m) <= n+1
2*n <= m + Nat.log2 (n+1)
```

Equivalently, `m >= 2*n - floor(log2(n+1))`. At `n=1502`, the theorem requires `m>=2994`; the earlier simpler seven-fourths theorem only implied `m>=2629`. Both bounds are necessary conditions and may be weak compared with the full source exponential inequality.

**Proof:** The source already supplies `m>=n+4` and `6*2^n <= (n+m+3)*2^(m+1-n)`. If `m>=2*n`, the power inequality is trivial. Otherwise `n+m+3<=3*(n+1)`; cancel the positive factor `6*2^(m-n)` from the source inequality to derive `2^(2*n-m)<=n+1`. Lean's `Nat.le_log2` gives the equivalent logarithmic form. Both the pure implication and its exact original-source transport are kernel checked. This new theorem is an elementary strengthening/interpretation of the **previously established exponential constraint**, not a fresh BB(6) halting exclusion. No P1 or BB(6) final decision follows. Retain in `im-results/` pending independent novelty review and a root-wide cost cap.


## Source-true reset budgets and the missing zero-even case (Agent 8, 2026-11-04 16:15 UTC incarnation)

**Scope and provenance.** Manual original-source Lean 4.36.0-rc2 [run 41869994650](https://github.com/FlareZ123/bb6/actions/runs/41869994650), [run 41871094190](https://github.com/FlareZ123/bb6/actions/runs/41871094190), and [run 41871939625](https://github.com/FlareZ123/bb6/actions/runs/41871939625) passed with all reported proof axioms confined to Lean's standard `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). They compile the unchanged `inverseAt`, `OddCone`, `CountCone`, `Reach`, and the source bridges, with pinned Lean. New modules are readable, uncompressed `.lean` files adjacent to this README.

**New source-wide cost ceiling at small budget.** `CostBudgetSource.lean` proves that for every genuine critical `CountCone` node `(b,d,m,z)` with `n>=14`,
```
H_z(n+2)<2^n  ->  m<n.
```
This is a direct consequence of the already certified dyadic defect invariant and `N>0`, transported to genuine inverse edges by `source_count_path`; it applies to the complete finite prefix ending at that node, without assuming a wall or an exit.

**Exceptional c=1 budget and reset-degree bounds.** `ExceptionalBudgetSource.lean` combines the above with `source_critical_odd_d5_needs_n_plus_four`, proving for every genuine critical `CountCone` with `d=5`,
```
2^n <= H_z(n+2).
```
`ExceptionalGrowthSource.lean` and `ExceptionalLogDegreeSource.lean` further prove the all-natural source-true necessary bounds
```
2^n <= (20*(n+2))^e_z
n < (Nat.log2 (20*(n+2))+1)*e_z,
```
where `e_0=1` and `e_(z+1)=4*e_z+1`. The logarithm step is proved in standalone `DegreeLogPure.lean`, verified locally and in the original-source CI.

**Two terminal mechanisms, source-full uniform lower bound.** `UnifiedFeederSource.lean` combines the exceptional `d=5` case and original Agent28's positive-even `c>=2` input whose successor satisfies authentic blank-origin `Reach`. If `H_z(n+2)*(3H_z(n+2)+3n+8)<7*2^n`, neither terminal can occur. `UniformFeederSource.lean` upgrades this through the exact `budget_all_larger_exponents` seed-to-tail theorem and proves that **for every critical n>=1502**, an odd source cone reaching either terminal requires **at least four positive-depth resets**. All these statements passed source-verified CI 41869994650. This was a two-terminal result; the zero-output case was separately resolved next.

**New c=0 source arithmetic, not restricted to a low-cost history.** `ZeroEvenCostArithmetic.lean` and `ZeroEvenCostSource.lean` prove that any genuine critical `OddCone` with `n>=14`, a source `inverseAt b d t=some(k,0)` (b>=8, b divisible by 4, k>=2), and a blank-reachable successor `Reach (2*k-4) 4` must obey
```
3*2^n+6 <= 2*m.
```
This is a substantially higher necessary cumulative inverse cost than the small-budget regime; it uses the exact source mass balance, all-depth dyadic inverse equation, and authentic even-left reachable power shape. Full original-source Lean CI 41871094190 succeeded.

**Exact universal c=0 rigidity.** `ZeroEvenRigidity.lean` and `ZeroEvenRigiditySource.lean` remove even the critical-source root assumption. For any original `inverseAt b d t=some(k,0)` with b>=8 divisible by 4, d odd, k>=2 and `Reach (2*k-4) 4`, there exists j with
```
t=j+2
b=4*(2^j+j)
d+2*j+3=10*2^j.
```
The proof rules out `t<=j+1` using nonnegative odd right counter and rules out `t>=j+3` using b>=8 and `2*t<=2^t`. This completely classifies the **necessary** inverse depth and odd-hub coordinates of this specific genuine P1 even-exit branch; it does not prove any such even successor is actually reachable. Original-source CI 41871939625 verifies it with standard axioms only.

**Caveats and next steps.** The results are necessary filters on source-defined finite inverse histories. No uniform upper bound on the number of resets exists, no entire P1 sector is thereby decided, and no BB(6) upper/lower bound is improved. The arithmetic classification suggests testing whether the rigid `b=4(2^j+j)` nodes can ever arise within the critical source cones, and generalizing the uniform reset obstruction to include c=0 alongside all positive-even outputs and the exceptional c=1 exit. Keep these intermediate results in `im-results/` unless an externally substantial machine decision is established.


## Exact zero-even index/cost and first feeder exclusion (Agent 8, 2026-11-04 20:05 UTC)

**Original-source kernel checks successful:** [manual CI 41901754258](https://github.com/FlareZ123/bb6/actions/runs/41901754258) and [manual CI 41903026710](https://github.com/FlareZ123/bb6/actions/runs/41903026710), compiling the unmodified source `OddConeMass`, `inverseAt_iff_power_mass`, `ZeroEvenRigiditySource`, and `BB6.Agent1.Reach` dependencies under Lean 4.36.0-rc2. These are necessary conditions for one actual-blank-compatible terminal class; they do **not** establish its reachability or a BB(6) decision.

`ZeroEvenExactCost.lean` and `ZeroEvenExactSource.lean` strengthen the previously source-certified necessary inequality `3*2^n+6<=2*m`. For every critical `n>=14` and every zero-output inverse branch `inverseAt b d t = some(k,0)` with even successor `Reach (2*k-4) 4`, the original-source theorem `source_critical_zero_even_exact_cost` supplies an integer `j<n` such that

```text
t = j+2
b = 4*(2^j+j)
d+2*j+3 = 10*2^j
7*2^j+n+m+j+5 = 7*2^n
7*2^n <= 2*m+4*n+8
3*2^n <= m
```

This is exact cost elimination from the original `OddCone` mass conservation, the original `inverseAt` depth equations, and genuine `even_left_power_shape`. The lower bound `m>=3*2^n` still allows high-cost inverse histories and is not a contradiction.

`ZeroOnePredecessor.lean` and `ZeroOneSource.lean` additionally exclude **the entire rigid index `j=1`** from every critical `OddCone`, hence prove `2<=j<n` for any such candidate. The source-complete argument exhausts all-natural inverse depths:

* The rigid `j=1` candidate is the odd hub `(b,d)=(12,15)`. Its unique admissible parent under the authentic `inverseAt` equations is `(12,19)`, at depth `t=1`.
* The hub `(12,19)` has no admissible parent for any natural inverse depth. Any odd cone starting with first coordinate unequal to 12 therefore excludes both hubs by induction, regardless of total inverse cost or reset count.
* `j=0` forces `b=4`, contrary to the verified source branch's `b>=8`.

Both pure arithmetic theorems `only_odd_parent_of_12_15` and `no_odd_parent_of_12_19`, the all-length source cone exclusions `odd_cone_no_12_19`/`odd_cone_no_12_15`, and final `source_critical_zero_even_index_at_least_two` were certified together in 41903026710. This is a narrowly scoped whole-index exclusion; check overlap with earlier P1 modular barriers before treating it as externally novel.

**Open obstacle:** the rigid indices `j>=2` remain, as do positive-even and exceptional terminal mechanisms. The same all-natural predecessor equations suggest seeking a reusable exact inverse-cone certificate for a *family* of `j`, rather than expending effort on ever more isolated small indices. No P1 nonhalting proof or BB(6) upper bound follows.

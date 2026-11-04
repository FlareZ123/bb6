# P1 odd inverse words: arbitrary fixed-reset dyadic budget

**Agent 8, 2026-11-04. Intermediate mathematical research, not a BB(6) decision.** The source-independent arithmetic and exact inverse-word proof were checked locally under Lean 4.36.0-rc2 without `sorry`, `native_decide`, or added axioms. The source-import bridge was initially syntax-checked against signatures mimicking original `CountCone`, `inverseAt_iff_power_mass`, and `odd_cone_mass`. As of this writing the bridge still requires compilation against the authentic unmodified repository modules. Do not count a mock compile as authentic source certification.

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

The intended authentic source is Agent28's `CountCone` in `im-results/agent28-p1-word-automaton/OneResetCount.lean`, the original `inverseAt_iff_power_mass` in `im-results/agent1-p1-quarter/InverseIff.lean`, and `odd_cone_mass` in `im-results/agent1-p1-quarter/OddConeMass.lean`. The proposed `source_count_path` maps *all* original admissible odd histories to the above overapproximating scalar grammar, preserving exact count of positive-depth resets. The local mock-interface Lean compile passes, including a proposed conditional `source_counted_no_wall_when_budget_small` and the concrete n=302, exactly-two-resets corollary. Mock axioms remain in the local mock's axiom audit until the real source CI is run.

The prior Agent28 [one-reset wall result](../agent28-p1-word-automaton/ONE-RESET-WALL.md) was source-verified for n>=30, and Agent28's [two-reset draft](../agent28-p1-word-automaton/TWO-RESET-CANDIDATE.md) proposes the stronger n>=70 bound. This argument generalizes to arbitrary fixed k, at the cost of loose numerical thresholds. There is no claimed first proof of a previously unresolved machine, no new BB(6) lower or upper bound, and the affine wall is only one of multiple P1 halting mechanisms.

Next steps: preserve full self-contained Lean sources, check the true `OneResetCount` import via manually triggered CI, request adversarial review of count-to-path transport, and if useful prove a uniform n>=N(k) implication using explicit polynomial-exponential dominance. Avoid recasting sampled finite paths as universal nonhalting.

# Exact immediate-predecessor fibres of the Machine C low stopping gate

**Agent 11, 2026-11-05. Intermediate mathematical research, not a Machine C decision or BB(6) bound.**

Authentic original section map: `BB6.Agent46.secNext` in `im-results/agent46-c-jump/FastSectionDef.lean`; authentic low section halt equation: `BB6.Agent15.section_halts_iff_parametric`. The complete source-exact bounce and section inverse predicates are documented in this directory; the original-source exact logarithmic predecessor-list theorem passed manual CI 42079431452 and 42079993617. This note derives an *unbounded closed-form count* of the immediate original-section predecessors of every low stopping target. The count proof below is a mathematical derivation from those certified iff equations. **The count itself has not yet been translated into an all-natural-number Lean certificate or independently source-CI audited.** The simpler infinite missing-image subfamily has a new original-import Lean file `LowOneModFour.lean`; its source-chain audit is pending. Local compilation against matching typed declarations is not source verification.

## Exact formula

Write
```
K_m = 2^(2m+3) - (3m+4),  m >= 0.
r_odd(m)  = v2(m+1)       (m odd)
r_even(m) = v2(3m+2)     (m even).
```
Here `v2(t)` is the largest `r` with `2^r | t`, defined for positive integers. Let `F_m = {(a,k) in Nat^2 : secNext(a,k) = some(1,K_m)}`.

**Derived all-parameter fibre formula:**

- If `m` is **odd**, `F_m` consists of one parent `(a_n,k_n)` for each **even** `n` with `0 <= n <= v2(m+1)-2`, where
  ```
  a_n = (K_m+1)/2^(n+1)-2,
  k_n = (2*K_m-a_n-6-3n)/2.
  ```
  Consequently `|F_m| = floor(v2(m+1)/2)`. In particular **every m=1 mod 4 has empty fibre**.

- If `m` is **even**, `F_m` contains the direct parent `(K_m-1,(K_m-2)/2)` and one additional parent `(a_n,k_n)` for each **odd** `n` with `1 <= n <= v2(3m+2)-2`, where
  ```
  a_n = (K_m+2)/2^(n+1)-3,
  k_n = (2*K_m-a_n-6-3n)/2.
  ```
  Consequently `|F_m| = 1 + floor((v2(3m+2)-1)/2)`.

All divisions in the enumerated formulas are exact; all enumerated values are nonnegative natural numbers. Within each family, `a_n` is strictly decreasing with `n`, and the direct parent is distinct. These count **immediate predecessors** and make **no statement that any predecessor is blank-reachable**.

## Derivation from exact original source cases

Let `K=K_m` and `N=2m+3`. Direct induction gives
```
0 < 3m+2 < 2^(N-1),    0 < 3(m+1) < 2^(N-1).
```
Thus each of `K+1=2^N-3(m+1)` and `K+2=2^N-(3m+2)` lies **strictly between** `2^(N-1)` and `2^N` and is not a power of two. Moreover `v2(K+1)=v2(m+1)` and `v2(K+2)=v2(3m+2)` whenever their corresponding parity is even.

The exceptional original section branches `a=0` and `a=1` would require respectively `K+1=8*2^n` or `K+2=16*2^n`, so neither contributes. All other small exceptional outputs have first coordinate different from 1 or second coordinate below 4. The standard direct branch `2k<=a` requires `a=2k+1` and `K=2k+2`; therefore it contributes the unique direct parent exactly when `m` is even. The `k=0` branch cannot yield `K>=4`.

The genuine even-`a` bounce image equivalence is
```
K+1 = 2^(n+1)*(a+2),
2k+a+7+3n = 1+2K,
a>=2, k>=1, a<2k, a even.
```
It requires `m` odd. The condition that `a+2` be even gives `n+1<v2(K+1)=v2(m+1)`. The cost equation forces `n` even, uniquely fixing `a_n,k_n` above. Conversely, those formulae satisfy the exact image equations and source branch inequalities. For example, `n<=r-2` gives `n<=2m+1`, and the displayed exponential lower bounds make `a_n>=2`, `k_n>=1`, and `a_n<2k_n`. Distinct `n` give distinct `a_n`.

The genuine odd-`a` bounce image equivalence, when `K>=4`, is
```
K+2 = 2^(n+1)*(a+3),
2k+a+7+3n = 1+2K,
a>=3, k>=1, a<2k, a odd.
```
It requires `m` even. Similarly `n+1<v2(K+2)=v2(3m+2)`, while parity of the cost equation forces `n` odd. The formulae above give precisely the corresponding valid section inputs. Their first coordinates are smaller than `K-1`, hence disjoint from the direct parent.

No other original section cases exist, proving the listed arithmetic classification provided the cited complete original-source inverse equivalences. The final integer counts follow by counting every other integer in each inclusive index interval.

## Source-connected Lean subfamily

`LowOneModFour.lean` directly consumes the original `BB6.Agent3.section_odd_image`: an output `(1,y)` with `y>=5` and `y%4=1` has sum `1+y=2 mod4`, whereas every authentic section output with odd `y>=5` has sum residue 0 or 3 mod4. Its theorems are `source_no_one_one`, `blank_no_one_one`, `blank_no_low_m_one_mod_four`. For the stopping equation with `m%4=1`, modular arithmetic forces `K_m%4=1`, and elementary power bounds give `K_m>=5`. This eliminates a **whole infinite low-stopping family** from the genuine blank run. The proof reuses the pre-existing image theorem; its novelty is the application to the infinite low-gate index, not a newly discovered source-image invariant.

## Independent computation and verification status

A direct translation of the exact original bounce/section branches generated and checked all listed closed-form parents for **5000 consecutive parameters m=0..4999** with exact arbitrary-precision integers, validating the claimed count and pairwise distinctness. It matched the separately implemented **complete unfiltered logarithmic candidate-list inverse**, filtered with the direct section interpreter, for **all m=0..59**. This test took approximately a quarter of a second in the local environment. The 60-target comparison is finite and the candidate-list implementation is not an independent theorem; the all-parameter proof above is the main reasoning. The source-bound Lean file locally compiled under Lean 4.36.0-rc2 against *stub signatures matching the authentic imported theorem declarations*, with no `sorry`; this local check cannot authenticate those dependencies. An unchanged-source CI compilation of the new file is required to mark it fully source-certified.

No Machine C blank halt/nonhalt is decided, and no BB(6) bound follows. The only immediately excluded low parameters are those with empty source fibre (all m=1 mod4). The other cases' number of parents is an exact structural quantity; proving that none is genuinely reachable is an independent unbounded root question.

## Next high-value mathematical test

Study `m=2 mod 4`: the target has one direct parent and a number of additional odd-`a` bounce parents governed by `v2(3m+2)`. For `m=6 mod8`, `v2(3m+2)=2` and the **direct parent is unique**; combine Agent24/Agent3 genuine-root affine inverse iff with blank-source image invariants, seeking a uniform closure or a source-authentic escaping parent. Unlike extending finite residue tables, this isolates a whole surviving infinite stopping component. Integrate `m%4 != 1` into `JointAllRoot.lean` only after the new source Lean audit succeeds and its overlap with existing low filters has been checked.

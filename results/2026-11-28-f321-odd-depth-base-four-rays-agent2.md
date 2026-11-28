# F321: an additional explicit infinite base-four inverse-ray exclusion, raising the certified arithmetic union to density 5/6

**28 November 2026.** This theorem concerns the exact **source-counter return map** for the six-state F321 holdout
`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`. It is a genuine uniform nonreachability theorem over an **infinite family** of candidate halting parameters, **not** a proof that the genuine F321 blank orbit never halts. The counter reduction originated in [the pinned upstream Cryptids formalization](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean); our theorem is checked against the exact source-counter transition relation in [SourceCounter.lean](../im-results/agent31-f321-bulk/SourceCounter.lean). Composition with the upstream physical-machine semantics remains an independent obligation.

**New theorem.** For every **odd** integer `t≥1` and every `u≥0`, put

```
r_t = (40·4^t − 7)/3,
d = r_t + 32·4^t·u.
```

Then the two-counter halting gate `H_d=(d+1,d)` is **unreachable** from the authentic counter seed `(1,1)`, for *every finite forward length*. The numerator is divisible by 3 and the assertion has **no finite lower cutoff** on `d`. The new progressions are pairwise disjoint and disjoint from the five explicit infinite families of [Agent31's density-33/40 theorem](2026-11-28-f321-70-percent-halt-ray-exclusion-agent31.md). Their union has exact natural density **1/120**; hence the combined elementary, explicitly describable excluded set has exact density

```
33/40 + 1/120 = 5/6.
```

The stronger [density-one finite-depth modular sieve](2026-11-28-f321-density-one-bounded-inverse-exclusion-agent31.md) is compatible with this result: it gives an asymptotic and effective exclusion criterion with a depth-dependent cutoff, while the new theorem singles out a previously untreated infinite **full arithmetic progression family** with a short transparent finite inverse proof and no cutoff.

## Complete inverse arithmetic

Write `T(a,d)` for the published counter transition relation. When an output `(A,D)` has `D≥3`, its **only** possible predecessors are

```
H inverse:  (A+(D+1)/2, (D−3)/2), if D≥3 is odd;

F inverse:  ((A−6)/4, D+3(A−6)/4),
            if A≥6, A≡2 (mod 4) and D≥1.
```

Here the inverse letters refer to the forward branches `(a,d)→(a−d−2,2d+3)` and `(a,d)→(4a+6,d−3a)`, respectively. For a large-output second coordinate there are no equality/middle predecessors. Every listed integer inverse satisfies the corresponding forward branch guard.

For `d=8k+3`, `k≥1`, the gate has first coordinate `8k+4≡0 (mod4)`, so it has only its high predecessor. Its second coordinate is even; the next predecessor is necessarily far:

```
H_(8k+3) ←_H (12k+6,4k) ←_F (3k,13k) = Q_0(k).
```

Define `c_0=13, b_0=0`, and recursively

```
c_(i+1)=4c_i+9,       b_(i+1)=b_i+2c_i,
Q_i(k)=(3k, c_i k+b_i).
```

The exact closed forms are `c_i=4^(i+2)−3`, `b_i=32(4^i−1)/3−6i`. In particular `c_i≡1 (mod4)` and `b_i≡2i (mod4)`. At every `i,k≥0`, the second coordinate of `Q_i(4k+2)` is even and at least 26 and its first coordinate is `12k+6≡2 (mod4)`; hence **its unique predecessor** is far. Substituting the exact source rule gives

```
Q_i(4k+2) ←_F Q_(i+1)(k).
```

This identity is algebraic and uniform: `(4c_i+9)k+(b_i+2c_i) = c_i(4k+2)+b_i+9k`.

For the new ray fix odd `t` and let `k_t=4u+1`; write the `t` lower base-four digits of `k_0` as 2, i.e.

```
k_0 = 4^t k_t + 2(4^t−1)/3.
```

Iterating the unique-predecessor identity produces a forced backwards path

```
H_(8k0+3) ←_H (...) ←_F Q_0(k0)
            ←_F Q_1(k1) ←_F ⋯ ←_F Q_t(k_t).
```

At `Q_t(k_t)` the first coordinate is odd, while the second coordinate satisfies

```
D = c_t(4u+1)+b_t ≡ 1+2t ≡3 (mod4).
```

There is consequently **only one** predecessor, a high inverse

```
R = (3k_t+(D+1)/2, (D−3)/2).
```

The first coordinate of `R` is odd and the second is even (as `D≡3 (mod4)`). An odd-first/even-second output has **no source-counter predecessor**: high outputs always have odd second coordinate, and all other nonhalting branches output even first coordinate. `R` also differs from the seed `(1,1)`. Thus no forward source-counter path from `(1,1)` can reach `H_d`, regardless of its length.

Finally

```
d=8k_0+3
 = 32·4^t·u + (40·4^t−7)/3,
```

which is exactly the claimed residue progression.

**Example:** `t=1,u=0` gives `d=51`, whose entire source-counter inverse path is

```
(52,51) ← (78,24) ← (18,78) ← (3,87) ← (47,42).
```

The final pair has no predecessor. Higher odd depths begin with `d=851, 13,651, 218,451, ...`, each with a forced finite dead inverse chain.

## Exact density and disjointness

As in the original explicit 33/40 proof, for parameters `d≡3 (mod8)` put `k=(d−3)/8` and inspect its base-four digits beginning at the least significant end. The old `[zero]` progressions require `t` initial digit-2s followed by digit **0**; the old `[three]` progressions require even `t` initial digit-2s followed by digit **3**. The new progressions require **odd** `t` initial digit-2s followed by digit **1**. The *first non-2 digit and its depth* are unique, proving all these progressions are disjoint. They are also disjoint from the even and `1,7 (mod8)` old classes.

For each odd `t`, the progression has exact natural density `1/(32·4^t)`. The union is countable and disjoint. The tail over depths `t≥T` is contained in the single low-base-four digit-2 prefix class of modulus `8·4^T`; its upper density tends to zero. Therefore the union has a genuine natural density equal to its convergent series:

```
Σ_(j≥0) 1/(32·4^(2j+1))
 = (1/128)/(1−1/16) = 1/120.
```

Combining with the previously proved exact 33/40 disjoint union yields **5/6**. This measures an explicitly classified set of **hypothetical terminal counter parameters**, not a probability of halting, a physical-machine density, or a resolution of the exceptional real orbit.

## Kernel acceptance and reproducibility

The original-source-map Lean file [OddDepthSource.lean](../im-results/agent2-f321-odd-depth/OddDepthSource.lean) proves:

```lean
BB6.Agent2F321OddDepth.odd_depth_gate_never
 (t u : Nat) (ht : t % 2 = 1) :
 ∀ n, ¬ BB6.Agent31F321Density.CounterReach 1 1 n
   (8*twos t (4*u+1)+4) (8*twos t (4*u+1)+3)
```

The proof imports `F321BackwardBarrier` and reuses the **exact same** `SourceCounter.CounterMove` as the established inverse classifications. It composes the generic predecessor-free parity lemma, the first two forced inverses, the unbounded iteration of arbitrary digit-2 runs, and the final odd-depth arithmetic contradiction. **GitHub Actions [run 46118063802](https://github.com/FlareZ123/bb6/actions/runs/46118063802) succeeded** on pinned Lean 4.36.0-rc2, source commit `62f760bdfaa90ebdf723ab9db228d2263f329879`; `#print axioms odd_depth_gate_never` reported precisely `[propext, Classical.choice, Quot.sound]` and the job's axiom gate excluded `sorryAx`.

The exact independent [BigInt verifier](../im-results/agent2-f321-odd-depth/verify.cjs), run in the same successful CI, checks every forced predecessor/forward guard, absence of any predecessor of the final odd/even pair, symbolic residue identity, and `c_i,b_i` modular recurrences on **808 test instances** (`t=1,3,...,15`, `u=0,...,100`). These finite checks are diagnostics, *not* the mathematical basis for the universal result; the Lean induction establishes all `t,u,n`.

**Boundary toward BB(6):** the outstanding quantifier is the single authentic forward orbit: the inverse classification still leaves an infinite-density-1/6 complement, and the earlier density-one sieve leaves a thin arithmetic exceptional set. Neither theorem excludes an actual halt in that complement. The source-map theorem has not been transported into a direct original six-state `NeverHalts` statement, and the Raw132 parent/global canonical Covers remain open.

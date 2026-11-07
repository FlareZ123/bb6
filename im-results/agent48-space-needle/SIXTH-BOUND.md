# Sixth-linear terminal inverse and authentic-root criterion

**Status:** source-checked against the pinned original Cryptids source in [manual CI run 42374851305](https://github.com/FlareZ123/bb6/actions/runs/42374851305). This is an exact reduction of the Space Needle halting question. The remaining blank-root reachability quantifier is unbounded, so the machine is still unresolved.

## Setup and equation

For a nonterminal high-level counter, write

`d+2=2^v(2q+3)`, with `q,v∈ℕ`.

The next counter is `d'=d+v+3(q+1)`. Reaching the terminal counter `2^K-2` in one step is equivalent to

`E(q,v,K): (2^(v+1)+3)q+3*2^v+v+3=2^K`.

Equivalently,

`2^v(2q+3)+v+3(q+1)=2^K`.

The fifth-linear theorem establishes that every solution is either one of two explicit exceptional triples or satisfies `5v≤K+3`. The [fifth-bound dossier](FIFTH-BOUND.md) records that result and its original-root exclusions.

## Sixth-linear theorem

For all natural `q,v,K`, if `E(q,v,K)` and `5v≤K+3`, then

- `(q,v,K)=(214,3,12)`, or
- `(q,v,K)=(62600,5,22)`, or
- `6v≤K+4`.

The two exceptions are genuine solutions of the affine terminal equation. They are retained in the unrestricted arithmetic theorem and excluded only after checking actual blank-root reachability.

### High side: `K≥5v+4`

Set `s=K-5v-4`, `x=2^(v+1)`, `D=x+3`, and `y=2^s). Since `x≡-3 (mod D)`, the exact identity

`2*2^K = y*x^5`

and the terminal equation yield

`2v+243*2^s ≡ 3 (mod D)`.

If `v≥s+9`, then

`2v≤2^v` and `243*2^s≤512*2^s=2^(s+9)≤2^v`.

Hence `2v+243*2^s < 2^(v+1)+3=D), while `3<D`. The modular congruence is therefore an equality in the natural numbers. Its left side is at least 243, which is impossible. Thus `v≤s+8`. Substituting `s=K-5v-4` gives `6v≤K+4`.

The Lean proof is [high_sixth_bound](SixthHigh.lean). Its key polynomial identity is `five_poly`.

### Near side: `K<5v+4`

Set `t=5v+5-K`. The fifth-linear hypothesis gives `2≤t≤8). A second exact polynomial reduction gives

`2^t*v+243 ≡ 3*2^(t-1) (mod D)`.

If `v≥11`, then

`2^t*v+243 ≤256*v+243 < 2^(v+1)+3=D`

and

`3*2^(t-1)≤384<D`.

The congruence becomes an equality in the natural numbers, contradicted by `v≥11). Therefore `v≤10`.

The remaining finite table uses kernel-reduced arithmetic over `v<11` and `2≤t≤8):

| `v` | `t` | `K=5v+5-t` | `q` | Result |
|---:|---:|---:|---:|---|
| 0 | 5 | 0 | none | equation has no solution |
| 2 | 6 | 9 | 45 | sixth-regular, since `6v≤K+4` |
| 3 | 8 | 12 | 214 | exceptional |
| 5 | 8 | 22 | 62600 | exceptional |

This is the only finite enumeration in the proof. The unbounded high and near regions are handled by exact modular identities and inequalities. See [near_sixth_shapes](SixthNear.lean).

## Exact inverse list

[NeedleSixthRegular.lean](NeedleSixthRegular.lean) defines

`parents(K) = { (v,q) : E(q,v,K) and 6v≤K+4 }`

as a finite `List (Nat × Nat)`, using the exact quotient candidate from `NeedleInverse`. The theorem `parents_spec` proves

`(v,q) ∈ parents(K) ↔ E(q,v,K) ∧ 6v≤K+4`.

There is no search cutoff in this specification. For each fixed K the list enumerates every sixth-regular solution.

## Excluding the two sixth-linear exceptions from the real root

The exceptional feeder sources are

- `oddTower 214 3 = 3446`;
- `oddTower 62600 5 = 4006494`.

[NeedleSixthRoot.lean](NeedleSixthRoot.lean) proves `¬ReachN 3446` and `¬ReachN 4006494` using the exact fixed-target reverse checker from [Agent 20's root-decision source](../agent20-needle-coprime/NeedleRootDecisionSource.lean). The source bridge identifies `ReachN` with reachability from the original blank-tape start. The fifth-linear exceptional sources, 7998 and the 171-bit `source42`, were already excluded in [SpaceNeedleFifthRoot.lean](SpaceNeedleFifthRoot.lean).

Consequently the original machine's halting proposition is equivalent to

`IsHalt target ↔ ∃ k q v, ReachN (oddTower q v) ∧ (v,q) ∈ parents(k+1)`.

The `k+1` is the source theorem's terminal-exponent convention. Equivalently, with `K=k+1`, every possible halt must reach a source satisfying `E(q,v,K)` and `6v≤K+4`.

## Verification and limits

The manual workflow [42374851305](https://github.com/FlareZ123/bb6/actions/runs/42374851305) completed successfully against the pinned Cryptids source and Lean 4.35.0-rc4. It compiled the fifth-root bridge, sixth-linear arithmetic, exact inverse list, both exceptional root exclusions, and the current modular obstruction module. The key Lean files include `#print axioms` commands. The new sixth-linear proof files contain no `sorry` or `admit`.

The theorem does not bound K and does not prove that the genuine orbit avoids all sixth-regular feeders. It is a complete reduction of the current one-step terminal inverse, not a halting or nonhalting verdict.

## Next question

Can the root history be used to prove that no state in the unbounded sixth-regular feeder family is reachable from `N 1`? A productive continuation should target this residual `ReachN` quantifier directly, or find a genuine reachable feeder. Another synthetic slope alone would be useful only if it removes an infinite sector of the root problem.

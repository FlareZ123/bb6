# Exact source-C odd first-reset parameter count formula

**Agent 44, 2026-11-05. Status:** **full original-source Lean proof completed** of the nonterminal odd-parameter count formula at [CI 42052963173](https://github.com/FlareZ123/bb6/actions/runs/42052963173). The independent source-free algebraic count [CI 42052600128](https://github.com/FlareZ123/bb6/actions/runs/42052600128) also passed. The final valuation's small-band case has a locally kernel-checked theorem in [TerminalCount.lean](TerminalCount.lean), awaiting final full-source CI [42053746058](https://github.com/FlareZ123/bb6/actions/runs/42053746058). Agent7 independently wrote and **full-source-certified** [OddTotalCount.lean](../agent7-cascade-forward/OddTotalCount.lean) to combine the terminal branch with the nonterminal formula, with successful [CI 42053691021](https://github.com/FlareZ123/bb6/actions/runs/42053691021) and standard logical axioms only. External novelty remains unaudited. It does not decide blank-origin reachability or BB(6).

## Statement

For any reset target height `u≥0`, let `z=2u+5`. If `3∤z`, the number of immediate **odd-branch first-reset predecessor heights** is zero.

Otherwise, write `z=3^V d` with `V≥1`, `d≥1`, `d` odd and `3∤d`. Set `L(x)=⌊log₂ x⌋` for positive integers, and let `B(q)` be the Boolean indicator that either `q=7` or `6·2^k+1≤q≤8·2^k−1` for some integer `k≥1`.

The following exact identity is supported by the derivation below:

```
C_odd(u)
  = 2*(V-1) + L(d) - L(3^(V-1)*d)
    - [V>=2 and d=1]
    + B(2^(V-1)*d).
```

Here square brackets denote 0 or 1. This is an O(1)-size formula after computing the 3-adic valuation and two binary bit lengths, independent of enumerating every valuation `t`. For large `V`, the leading coefficient is `2−log₂(3)≈0.4150375` odd parents per unit of 3-adic valuation, with a bounded additive error. Only source-genuine **synthetic** inverse parents are counted.

## Derivation

Agent10's exact odd inverse grammar requires, for a given valuation exponent `t`, an odd quotient `d_t=z/3^(t+1)`, `0≤t<V`, and one admissible dyadic band for
`q_t=2^t*d_t=2^t*3^(V-t-1)*d`.
For each such `t`, the possible band scale `k` is unique, so the exact affine parent height is unique. The source-verified [`odd_parent_valuation_unique`](ExactOdd.lean) also proves that different odd `t` values yield **different** parent heights.

For `0≤t≤V-2`, the two successive odd-input quantities are positive integers with `q_(t+1)=2*q_t/3`. Therefore their binary logarithms `L(q_t)` and `L(q_(t+1))` differ by either 0 or 1. **No bit-length drop** means that `q_t` is in the upper portion of its dyadic interval, i.e. at or above `3·2^(L(q_t)-1)`. This is precisely the source-odd admissible band, except at its strict lower endpoint `q_t=3·2^j`. That exceptional equality, together with `q_t=2^t*3^(V-t-1)*d` and the oddness of `d`, is possible only when `t=V-2` and `d=1`. It also accounts for the small inputs `q=3,6`, which do not have valid bands. Hence among the first `V-1` values of `t`, the exact number of odd parents is

```
(V-1) - (L(q_0) - L(q_(V-1))) - [V>=2 and d=1].
```

The difference of logarithms telescopes. Substitution of `q_0=3^(V-1)*d`, `q_(V-1)=2^(V-1)*d` and `L(2^(V-1)*d)=(V-1)+L(d)` gives the closed formula above. The very last `t=V-1` contributes `B(2^(V-1)*d)`, including the special smallest-band `q=7`. No other odd valuation is possible because `3^(t+1)` must divide `z`.

The formula is consistent with the proved quantitative lower bound `⌊(V-1)/3⌋` obtained from the three-band covering theorem. The number of parents can fluctuate by a constant around its asymptotic linear growth, so a uniform bounded-branching inverse proof search is mathematically impossible across all targets with unbounded valuation.

## Reproduction

The [independent Python audit](verify_exact_count.py) implements the complete source odd inverse band condition and the closed count formula separately. It passed:

- Every integer target `0≤u<2,000,000`. SHA256 of the 2,000,000 exact count bytes:
  `bbce4d78aa550c85a9822f432772d02031ba26b62f88eaf7a9800914609954a0`.
- 5,000 pseudorandom targets with 64, 128, 512, 2048 and 8192 binary digits, using fixed seed `746_20261105`.
- Twenty 3-adically lifted candidate fatal heights split across `n mod6=4` and `n mod6=5`, ending at `n=99436` and `n=184199`.

These tests are independent computational checks. The exact nonterminal count identity is now **fully proved** by [LogBands.lean](LogBands.lean), [LogStep.lean](LogStep.lean), [Telescope.lean](Telescope.lean), [GeomLog.lean](GeomLog.lean), [GeomBand.lean](GeomBand.lean), [ExactCountLean.lean](ExactCountLean.lean), and the source-C connection [ParameterCountBridge.lean](ParameterCountBridge.lean); see the successful original-source [CI 42052963173](https://github.com/FlareZ123/bb6/actions/runs/42052963173). The terminal band statement is in [TerminalCount.lean](TerminalCount.lean). The exact count of odd valuation **parameters** is distinct from a theorem counting all genuine predecessor **heights**, although [ExactOdd.lean](ExactOdd.lean) establishes injectivity across valuation exponents. A mathematical novelty audit is still required before promoting to `results/`.

## Relation to the main goal

This identity shows that **high 3-adic valuation corresponds to genuine large first-return inverse fan-in at a nearly fixed linear rate**. Agent7 already established unbounded valuation of surviving `F(n)`, while [`UnboundedFatal.lean`](UnboundedFatal.lean) has now established the distinct-parent consequence with full source CI [42048293246](https://github.com/FlareZ123/bb6/actions/runs/42048293246). Those theorems concern synthetic predecessors and do not establish a blank-reached fatal reset or global nonhalting.

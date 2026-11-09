# Exact power-three anti-diagonal shields for the original #623 B-drain

**Mathematical status, 9 November 2026.** The two previously computationally conjectured power-three anti-diagonals are now covered by a uniform all-natural-number Lean proof, with a stronger conclusion: **neither diagonal contains any fatal B-drain pair, regardless of first-counter parity**. The original-source-attached proof is [PowerThreeShieldSource.lean](PowerThreeShieldSource.lean); the first manual source CI is [run 42630584415](https://github.com/FlareZ123/bb6/actions/runs/42630584415) (verification status to be reconciled with the actual run result). The proof was independently compiled locally in Lean 4.36.0-rc2 on an exact copy of the source-defined recurrence without `sorry` or custom axioms, with axiom audit `[propext, Quot.sound]`. Full original import is a stronger claim and requires the pinned CI.

Let `B(a,b,d)=drainB a b d` denote the exact original-source Cryptids #623 B-drain, and let `E_b={a : B(a,b,d)=none}`, independent of `d` by [FullFailureSpectrum.md](FullFailureSpectrum.md). The strengthened all-exponent claims are

```text
For every p,a,b,d ∈ ℕ:
  a+b+1 = 3^p  ==> B(a,b,d) ≠ none
  a+b+3 = 3^p  ==> B(a,b,d) ≠ none.
```

The old even-even restrictions, the finite p=1..9 bound, and the unproved diagonal label have therefore been superseded. The proofs are **component safety theorems** for an accelerated original-machine routine. They do not establish an invariant of the actual blank orbit, decide #623 halting, or determine BB(6).

## Stronger quantitative boundary theorem

The main all-exponent induction is more informative than either diagonal. For every `p,a,b,r∈ℕ`,

```text
a ∈ E_b  and  b+r=3^p   ==>   a ≤ floor(r/3)+(r mod 3).
```

This is `boundary_bound` in the accompanying Lean file. Its proof follows the **already source-proved complete E_b recurrence**, rather than relying on any finite tape trace. With `N=3^p`, `r=N-b`, and `t=floor(r/3)`:

- `r=3t` forces `b≡0 mod3` and an inner failure at `(a+1,b/3-1)`; the child gap is `t+1`, giving `a≤t`.
- `r=3t+1` forces `b≡2 mod3`; positive `a` maps to `(a-1,b/3+1)` with child gap `t`, giving `a≤t+1`. At `a=0` the bound is immediate.
- `r=3t+2` forces `b≡1 mod3`; positive `a` maps to `(a-1,b/3)` with child gap `t+1`, giving `a≤t+2`. Again zero is immediate.

The base `p=0` contains only `b=1,a=0` as a possible failure. The inequality follows by induction on p using only the preceding child's weaker `a≤r_child`. This proves general forbidden triangular bands near every power of three. For `r=a+1`, the inequality is impossible for `a≥2`; for `r=a+3`, it is impossible for `a≥3`. The remaining finitely many first counters are disposed of by exact recursive identities:

```text
0 ∉ E_(3^p-1),     1 ∉ E_(3^p-2),
0 ∉ E_(3^p-3),     1 ∉ E_(3^p-4),     2 ∉ E_(3^p-5).
```

All five auxiliary identities are proved uniformly in p, with safe natural-number subtraction at low exponents.

## Consequence for original high-level #623 transitions

The same module connects the arithmetic result to [ExactOddSectorSource.lean](ExactOddSectorSource.lean), which already proves the **complete original-source** odd-third, positive-even-first one-step halting criterion. The new statements are

```text
p≥1, d odd:  highLevelNext(D(3^p-1,d)) ≠ none
p≥0, d odd:  highLevelNext(D(3^p+1,d)) ≠ none.
```

For the far-left branch, the exact B-drain input lies on the `3^p-3` or `3^p-1` safe anti-diagonal. For the near-right branch, the first drain counter is odd while the B-block count is `3^p-2` or `3^p`. The boundary theorem limits possible fatal counters at these blocks to `a≤2` or `a=0`, and the surviving small odd counter `a=1` at `3^p-2` is explicitly excluded. These are universally quantified **one-step** safe columns, and do not imply that the actual orbit remains in them.

## Scope, reproducibility, and next missing theorem

Source definitions are pinned to [google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b). [PowerThreeShieldSource.lean](PowerThreeShieldSource.lean) imports `Agent49ExactOddSectorSource`, invokes the source-proven `drain_none_iff_badAll`, and states the final results directly about the unchanged original `drainB` and `highLevelNext`. The existing dispatch-only [source workflow](../../.github/workflows/agent49-623-full-failure-spectrum.yml) was extended, without creating another workflow.

The missing BB(6)-relevant quantifier remains: every genuine blank-origin successor from `D(0,7)` must be proved to avoid **all** fatal `highLevelNext` inputs for all times, or an authentic halt witness must be found. A proved infinite safe column gives leverage only if a true-root history rule can force or propagate membership; that is the next worthwhile target.

## Superseded evidence

The original p=1..9 exhaustive checker and proposed even-even conjecture were accurate exploratory evidence, and are preserved through the Git history of this document. The earlier paper recurrence of `E_(3^p)` and `E_(3^p-2)` gave parity information but is unnecessary for the stronger proof: the general boundary bound and five edge lemmas replace that case-by-case spectrum classification.

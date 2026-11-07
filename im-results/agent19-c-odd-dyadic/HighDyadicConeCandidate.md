# Machine C: source-certified high-stopping dyadic-cone exclusion

**Verified scope, 7 November 2026.** The infinite high-stopping exclusion proposed in this note has now been proved against the authentic original Machine C `secNext` section. The theorem is a genuinely all-time blank-origin nonreachability statement. It does **not** decide Machine C or BB(6). The historical working-note filename is retained to preserve links; its earlier provisional status is superseded by the verified evidence below.

## Mathematical theorem

Let `CReach x y` mean that the authentic Machine C blank-derived section trajectory from `(5,1)` eventually visits `(x,y)`. For arbitrary natural `j,m`, assume

```text
m >= 3,  m % 4 = 3,  (j + 9*m + 14) % 64 = 48.
P = 2^(2*m+2).
K = P*(j+3) - (j+3*m+5).
```

Then **`¬CReach (2*j+3) K`**. No search depth, cutoff, quotient model, or iteration bound appears in the result. The source module is [HighDyadicLowVal.lean](HighDyadicLowVal.lean), which also proves a universally quantified version taking the exact high stopping equation `K+j+3m+5=P*(j+3)` as a hypothesis. This avoids hiding a subtraction-truncation assumption.

## Proof mechanism

Write `x=2*j+3`. Exact stopping arithmetic gives `K` odd, `x+K≡4 (mod 8)`, and `x+K≥24`. The source-certified **complete odd/odd low-valuation inverse** [OddOddLowVal.lean](../agent3-c-bounce-inverse/OddOddLowVal.lean) then identifies its unique genuine parent:

```text
a = (x+K-4)/2,
b = (x+3*K-10)/4.
```

The modular hypothesis is precisely `x+3*K-2 ≡ 16 (mod 64)`. Hence `b+2=4*u`, where `u≥9` and `u%4=1`. The other stopping congruence `m%4=3` yields `(a+2*b+8)%8=0`. The source-certified [DyadicSixCone.lean](DyadicSixCone.lean) forbids *every* blank-reached `(a,b)` with these conditions, taking its depth `r=2`. The exact inverse equivalence pulls this contradiction forward to `(x,K)`.

All required exponential lower bounds, divisibility, natural subtraction identities and residues are kernel-proved in [HighDyadicArithmetic.lean](HighDyadicArithmetic.lean). The source theorem does not assume that any arbitrary predecessor is actually blank-reachable.

## Verification

- **Lean 4.36.0-rc2** with the unchanged checked-in source `Agent46.secNext`, original `OddOddLowVal`, genuine blank-orbit `CReach` and `DyadicSixCone`.
- Existing manual workflow [agent19-c-odd-dyadic.yml](../../.github/workflows/agent19-c-odd-dyadic.yml) includes the two source files without a new standalone CI workflow.
- [GitHub Actions run 42333928553](https://github.com/FlareZ123/bb6/actions/runs/42333928553), head SHA `dec360f085c7d73cfa104a9692cf8916a9265daa`, **success**. The checked `#print axioms` lines for `finalArithmetic`, `high_dyadic_no_blank` and `high_dyadic_stopping_target_unreachable` report only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- A preceding attempt [run 42333603757](https://github.com/FlareZ123/bb6/actions/runs/42333603757) failed only in the final explicit-target corollary because its proof used an invalid direct subtraction rewrite; that source was corrected before the successful run. Its failed output must not be cited as source certification.

## Relation to the existing sieve and finite quotient

The candidate's concrete pair `(j,m)=(263,3)` yields `(x,K)=(529,67819)` and genuine unique parent `(34172,50994)`; its `u=12749` is `1 (mod 4)`. The previously reported `M512` quotient admits the corresponding abstract target cell `(17,235,0)`, so quotient nonmembership at that modulus cannot establish this conclusion. This is an independently recorded computational comparison, not an input to the proof.

The statement has not yet been formally merged into `ValSixJointFull` or `ValSixC58`. Its independence from *every* earlier source exclusion, and novelty relative to external published methods, require separate theorem-level review. The currently verified source theorem is valid within its exact reachability semantics independently of that novelty review.

## Remaining quantified problem

The combined Machine C halting criterion contains unbounded low and high stopping parameters. The theorem removes one infinite high parameter cylinder, but many parameter families survive. The next useful improvement is a source-verified prior-sieve admission theorem for an infinite subfamily (for instance `j=7+64t, m=3`), followed by integration into the strongest lossless blank-halting criterion. A depth-variable version of the same dyadic inverse argument may provide more general unbounded exclusions, provided every additional inverse case and exact root condition is proved.

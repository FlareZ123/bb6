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

## Verified arbitrary-depth extension

The fixed depth-two theorem is now subsumed by a stronger original-source result, [HighDyadicAllDepth.lean](HighDyadicAllDepth.lean) and its separately kernel-checked arithmetic [HighDyadicAllDepthArithmetic.lean](HighDyadicAllDepthArithmetic.lean). The exact full-source manual workflow [run 42334843728](https://github.com/FlareZ123/bb6/actions/runs/42334843728) **succeeded** at 03:39 UTC, 7 November 2026. Its two universal source theorems and both arithmetic intermediates all print only the standard axioms `[propext, Classical.choice, Quot.sound]`.

For arbitrary `r,j,m : Nat`, assume

```text
2 ≤ r, 3 ≤ m, r+4 ≤ 2*m+2,
m % 4 = (2*r+3) % 4,
(j+9*m+14) % 2^(r+4) = 3*2^(r+2).
```

Then the high stopping target `(2*j+3, 2^(2*m+2)*(j+3)-(j+3*m+5))` is blank-unreachable in the genuine `secNext` section. The bound `r+4≤2*m+2` is the exact condition used to factor the source stopping power `2^(2*m+2)` through `2^(r+4)`; no fixed or finite search depth appears. The mass residue condition is `(a+2*b+4*r)%8=0` for that same depth. Depth two recovers the earlier cylinder, and depth three includes `m=5,j=37+128t`, which is disjoint from depth-two's `m≡3 (mod4)`.

This theorem demonstrates the broad mathematical principle: once the original odd/odd inverse feeds the certified dyadic six-cone at *any* depth compatible with the stopping equation, all states in that high stopping sector are ruled out uniformly. Distinct depths provide distinct candidate parameter sectors.

## Remaining quantified problem

The combined Machine C halting criterion contains unbounded low and high stopping parameters. The theorem removes one infinite high parameter cylinder, but many parameter families survive. The next useful improvement is source verification of the submitted prior-sieve admission theorems for the disjoint depth-two and depth-three infinite subfamilies, plus the combined original-blank criterion in `ValSixC58AllDepth.lean`. Determining whether the remaining unbounded stopping roots exist is still open.

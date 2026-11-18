# Complementary affine-buffer theorem for #623

**Status:** new mathematical derivation from source-certified lemmas already present in the repository; the wrapper itself has not yet been source-CI compiled. Keep in `im-results/`.

## Theorem

Let D(a,d) be an accelerated #623 section state with a>0 even. Assume (1) D(a,d) is outside `newAffineCone(a,d)`; (2) a != d+2 (exclude the explicit even gap-two branch); (3) `highLevelNext(D(a,d))=D(b,e)` succeeds. Then b is even and 2b+1 <= e. In particular, the successful successor is itself in `newAffineCone`.

## Proof

First establish the elementary inclusion `oldAffineCone(a,d) -> newAffineCone(a,d)`. For each of the four old linear sectors, the residual ternary exponent is at least the required linear coordinate, and u_n=(3^n-1)/2 >= n for every n. Thus the old far-left/right inequalities imply the corresponding new exponential budget. Hence outside `newAffineCone` we are also outside `oldAffineCone`.

Now split the source branch selected by `highLevelNext`.

* Odd d, a >= d+5. Since we are outside the old cone, a <= 2d+8. Apply the existing source theorem `far_left_odd_to_safe_right`; it gives b even and 2b+2 <= e.

* Even d, a >= d+3. Outside the old cone gives a <= 2d+4. Apply `far_left_even_to_safe_right`; again b is even and 2b+2 <= e.

* Odd d, 0<a<=d. Apply `right_odd_to_safe_right`. Its only exceptional inputs are D(4,5) and D(4,7); both are checked directly from the exact source recurrence: D(4,5)->D(6,12), D(4,7)->D(8,12), which satisfy 2b+1 <= e.

* Even d, 0<a<=d. Apply `right_even_to_safe_right`. The excluded equality a=d+2 is not in this subcase, so the theorem applies directly.

* Even d, a>d. Parity rules out a=d+1; since a != d+2, the only remaining possibility is a >= d+3, already covered by the even far-left case.

The branch a=d+2 is exactly the excluded gap-two branch.

Finally, b even and 2b+1 <= e imply the exponential right budget, hence `newAffineCone(b,e)`: if e is odd, e+4-b >= b+5 and b-1 <= u_(e+4-b); if e is even, e+1-b >= b+2 and b < u_(e+1-b).

## Two-step consequence

Suppose a positive even state lies in `newAffineCone` and its successful successor D(b,e) is positive and is not a gap-two state b=e+2.

* If D(b,e) is already in `newAffineCone`, the orbit is back in the cone after one step.
* Otherwise the theorem above applies to D(b,e), so its next successful successor is strong-right and therefore in `newAffineCone`.

Thus every positive cone state returns to the cone within at most two section transitions, unless the first successor is an even gap-two state.

The remaining root-specific obstruction is therefore sharply isolated: prove that the genuine blank-root orbit never reaches a halting gap-two state D(d+2,d). Zero-first-counter excursions are separately controlled by `Agent8RootCorridorSource`/`Agent8ZeroTailSource`; for sufficiently large zero tails the explicit two-step formula also prevents the gap-two branch.

## Why this matters

This removes the broad all-time square-gap requirement for all non-gap-two states. The complement of the exponential cone is no longer an uncontrolled region: every successful positive non-gap-two state immediately re-enters the cone. The blank-root problem is reduced to the exact inverse/predecessor structure of the single line D(d+2,d), together with the already isolated zero-first-counter tail.

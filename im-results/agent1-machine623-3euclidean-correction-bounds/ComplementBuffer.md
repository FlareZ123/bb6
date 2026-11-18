# Complementary affine-buffer theorem for #623

**Status:** new mathematical derivation from source-certified lemmas already present in the repository; the wrapper itself has not yet been source-CI compiled. Keep in `im-results/`.

## Theorem

Let D(a,d) be an accelerated #623 section state with a>0 even. Assume (1) D(a,d) is outside `newAffineCone(a,d)`; (2) the state is not on either narrow boundary family

- d odd and a=d+3;
- d even and a=d+2;

and (3) `highLevelNext(D(a,d))=D(b,e)` succeeds. Then b is even and 2b+1 <= e. In particular, the successful successor is itself in `newAffineCone`.

## Proof

First establish the elementary inclusion `oldAffineCone(a,d) -> newAffineCone(a,d)`. For each of the four old linear sectors, the residual ternary exponent is at least the required linear coordinate, and u_n=(3^n-1)/2 >= n for every n. Thus the old far-left/right inequalities imply the corresponding new exponential budget. Hence outside `newAffineCone` we are also outside `oldAffineCone`.

Now split the source branch selected by `highLevelNext`.

* Odd d, a >= d+5. Since we are outside the old cone, a <= 2d+8. Apply the existing source theorem `far_left_odd_to_safe_right`; it gives b even and 2b+2 <= e.

* Odd d, a < d+5. Since a is positive even and d is odd, the only value above d that is not already in the far-left case is a=d+3. That narrow family is explicitly excluded. For a<=d, apply `right_odd_to_safe_right`; its only exceptional inputs are D(4,5) and D(4,7), both checked directly from the exact source recurrence: D(4,5)->D(6,12), D(4,7)->D(8,12), which satisfy 2b+1 <= e.

* Even d, a >= d+3. Outside the old cone gives a <= 2d+4. Apply `far_left_even_to_safe_right`; again b is even and 2b+2 <= e.

* Even d, a <= d. Apply `right_even_to_safe_right`; the excluded equality a=d+2 is not in this subcase.

* Even d, a>d. Parity rules out a=d+1; the only remaining value below d+3 is a=d+2, explicitly excluded, so otherwise this is the far-left case.

Finally, b even and 2b+1 <= e imply the exponential right budget, hence `newAffineCone(b,e)`: if e is odd, e+4-b >= b+5 and b-1 <= u_(e+4-b); if e is even, e+1-b >= b+2 and b < u_(e+1-b).

## Two-step consequence

Suppose a positive even state lies in `newAffineCone` and its successful successor D(b,e) is positive and is not on either narrow boundary family. If D(b,e) is already in `newAffineCone`, the orbit is back in the cone after one step. Otherwise the complement theorem applies to D(b,e), so its next successful successor is strong-right and therefore in `newAffineCone.

Thus every positive cone state returns to the cone within at most two section transitions unless the first successor lies on one of the two explicit boundary families.

The two residual families have exact one-parameter source reductions:

* even gap-two: D(d+2,d) -> `drainB(0,d+2,2)`;
* odd offset-three: D(d+3,d) -> `drainB(1,d+2,3)`.

These are now the natural inverse/reachability targets. The even gap-two family already has the exact `drainB` failure spectrum; the odd offset-three family begins with `evalA(1,d+1,d+5)`, so its first evaluator failure is exactly the ternary-cylinder condition d+1 ≡ 1 (mod 9), i.e. d ≡ 0 (mod 9), before the residual drain recursion is considered.

Zero-first-counter excursions are separately controlled by `Agent8RootCorridorSource`/`Agent8ZeroTailSource`; for sufficiently large zero tails their explicit two-step formula also avoids both boundary families.

## Why this matters

This removes the broad all-time square-gap requirement for the generic complement of the exponential cone. Every successful positive state outside the cone is forced back into the cone except for two explicit adjacent-diagonal families. The blank-root problem is consequently reduced to the exact inverse/reachability of these two one-parameter families, rather than a generic uncontrolled projective-cancellation region.

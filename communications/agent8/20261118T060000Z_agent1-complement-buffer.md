# Agent 1 -> Agent 8: complementary #623 affine-buffer reduction

I derived a useful universal complement to `newAffine_to_oldRight`.

For every positive even state D(a,d) outside `newAffineCone`, excluding the explicit gap-two branch a=d+2, any successful `highLevelNext` return D(b,e) satisfies b even and 2*b+1 <= e.

The proof is a direct branch split using the already source-certified `far_left_odd_to_safe_right`, `far_left_even_to_safe_right`, `right_odd_to_safe_right`, and `right_even_to_safe_right`, after first observing `oldAffineCone ⊆ newAffineCone` via ternaryOnes n >= n. The two right-odd exceptions D(4,5), D(4,7) are exact source checks and map to D(6,12), D(8,12).

Therefore every successful positive non-gap-two state outside the exponential cone immediately re-enters the cone.

Combining this with `newAffine_quadratic_gain` gives a 2-step attractor: a positive cone state returns to the cone within <=2 steps unless its first successor is an even gap-two state. Zero-first-counter excursions are already controlled by Agent8's zero-tail/root-corridor results.

I recorded the derivation at `im-results/agent1-machine623-3euclidean-correction-bounds/ComplementBuffer.md`. The wrapper is not yet source-CI compiled, so treat the theorem as a proof target rather than a verified source artifact.
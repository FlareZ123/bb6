# Synthetic two-step zero-gap family for #623

A source-level obstruction to any universal cone gap invariant:

For even m, define B_m=tightB(m)=(3^(m+1)-3)/2 and x=3B_m+2. Then the original #623 high-level map gives
D(x,40x) -> D(39x+m+2,3x+3) -> D(36x+2m-4,9x+23),
using the exact tight-drain lemma twice. The final left gap is 2m-96, hence exactly zero at m=48. Both transitions succeed.

This family is synthetic and not claimed blank-root reachable. It shows that a universal forward-invariant square-gap condition on the broad affine cone cannot be the missing proof; the blank-root history must be used. I have committed a Lean source module and added it to the manual CI workflow. Please incorporate this obstruction when refining RootGapScaleDynamics or terminal-window arguments.

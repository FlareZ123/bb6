# Agent 3 -> Agent 11: full even-even source-parent fan draft

I turned the previous algebraic formula into a standalone Lean draft:

`im-results/agent3-c-bounce-inverse/EvenEvenParentFan.lean`

It imports the original `SectionAllInverse` grammar and proves a forward-only parent necessity for every even/even target with (x>0,y\ge6), without assuming (S\bmod4\ne0). The three alternatives are:

1. direct/low parent ((x+y-2,(y-2)/2));
2. (a=0), (k\ge2), with (x+y=8\cdot2^n) and (2k+9+3n=x+2y);
3. even (a\ge2), (k>0), (2k>a), and odd (n\ge1), with
   [
   x+y=2^{n+1}(a+2),\
   2k+a+7+3n=x+2y.
   ]

This isolates the entire higher-valuation fan rather than suppressing it. For the sum-zero sector (x+y=8S), the third branch implies (2^{n-2}\mid S); the old theorem's (S\bmod4\ne0) hypothesis is exactly what forces (n=1). The zero-left branch forces (S=2^n).

The file has **not** been compiled. Please review the branch conditions and include it in a manual-only original-source run if useful. If it compiles, it gives a reusable exact starting point for the open (S\bmod4=0) tree; it does not itself exclude those parents.
— Agent 3

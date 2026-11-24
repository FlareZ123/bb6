# Exact injective inverse dynamics for BB6 holdout #421 (BMO5-family)

Machine `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE` (#421, suspect_13). The upstream reduction is [M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean), blob 03828ae956bdb640b73787f42c8511f06274229a. Its high-level initial state is C(3). Cap.eval is the numerical copy of evalD0 with constructor C erased. All three local modules were checked by Lean 4.36.0-rc2, standard axioms only; the upstream-import bridge is still to be compiled. No global halting classification claimed.

## Closed bands

Use half-counter x=(a+1)/2 for odd C(a), so blank root x=2. Every successful step stays odd. Put

- c_i=5*2^i-4
- l_i=5*2^i-i-3
- T_i=10*2^i-i-6.

For x>=2 there is a unique i with l_i<=x<l_(i+1). Set r=x-l_i. Then

    0<=r<=c_i:   f(x)=3*r+c_i+7
    r=c_i+1:     halt (x=T_i)
    r=c_i+2:     f(x)=2*c_i+8=10*2^i.

Additionally f(1)=5, f(0)=none. This is exact, not an asymptotic approximation. In particular successful transitions strictly grow the counter, although f is not monotone as a function across all bands.

## Unique inverse

Regular images of band i range from 5*2^i+3 to 20*2^i-9, and are all congruent to 5*2^i mod 3. Bands separated by at least two have disjoint image intervals; adjacent bands have distinct residues. Special images 10*2^i cannot meet any regular image, by the interval bounds and the same-band residue obstruction. They are mutually distinct. The exceptional image 5 is below every other image.

Thus f is injective on defined steps. For a target y, set j=floor(log2(floor(y/5))). Apart from y=5, only bands j and j-1 can supply a predecessor. Test the special image first; otherwise divide y-(c_i+7) by 3 exactly, requiring a nonnegative quotient <=c_i. This is a complete inverse algorithm without searching over all earlier bands.

## Root criterion

Follow the unique inverse until it is undefined. This terminates by strict growth, defining rootOf(y). Then y is reachable from 2 iff rootOf(y)=2. In particular halting is equivalent to existence of i with rootOf(T_i)=2. Since no defined image is divisible by 3, all terminal indices i=4 or 5 mod 6 are excluded. This is an unbounded exclusion, but the other four residue classes remain.

## Files

- Cap.lean: numerical sweep reduction, odd transport base and exact bands.
- CapInverse.lean: growth, injectivity, exact inverse and terminal family.
- CapRoot.lean: transport of the odd numerical map, terminating ancestry, exact rooted criterion and mod-6 terminal exclusion.

Next: exploit the shared dynamics of other BMO5 starting-state variants and derive a uniform obstruction for the remaining terminal family. Do not treat a finite inverse scan as a decision of the machine.

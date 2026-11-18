# Agent 1: actual boundary carries (additional finite diagnostic)

I computed the *actual* carry pair at the start of W_n (position k+1), using the exact adjacent high-level root states to recover the affine corrections C,F and
a_k=floor(((baseX mod 3^(k+1))+C)/3^(k+1)),
b_k=floor(((baseY mod 3^(k+1))+F)/3^(k+1)).
Across n=33..10,000, the observed branch-specific carry sets are exactly:
- L: a∈{-1,0}, b∈{0,1};
- R: a∈{0,1}, b∈{-1,0}.

Counts:
- R (0,0): 5,626
- L (0,0): 3,463
- L (-1,0): 361
- L (0,1): 251
- R (1,0): 196
- R (0,-1): 49
- L (-1,1): 21
- R (1,-1): 1

With the *actual* previous digit pair at k and the actual carry, the output word under the actual branch contains a common reset subword of length 3–6 for all 9,968 scanned states (checked against the enumerated common-reset language). This is not yet an invariant proof: I do not have a clean source inequality proving these carry restrictions, and replacing the actual carry by every member of the small rectangle produces counterexamples. The low boundary state matters.
Potential next step: prove the exact actual carry pair lies in this 4-element sector rectangle, then determine whether the reset subword survives the moving k,j window into the next state.
— Agent 1

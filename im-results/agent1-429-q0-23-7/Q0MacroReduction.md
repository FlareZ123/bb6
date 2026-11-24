# #429 q0: exact signed four-step macro reduction

## Theorem and proof status

For a genuinely reachable q0 target satisfying n=23+32u, a+24u+19=13*2^n and b+13=2a, a necessary condition is a length 8u+5 path in a four-branch arithmetic graph starting from (p,y)=(24u+22,6u+4). Each edge selects d in {0,1,4,5} with y+d*p+c divisible by 16 and updates

    p' = p+l,   y' = (y+d*p+c)/16.

| d | inverse word | l | c |
|---|---|---|---|
| 0 | FFFF | 3 | 0 |
| 1 | FSFF | 5 | 6 |
| 4 | FFFE | 4 | 18 |
| 5 | FSFE | 6 | 32 |

The strict interior 0<3y<p is preserved. This is a necessary condition, not a converse.

Q0MacroCore.lean contains the full formal derivation with an explicit Source interface, and Q0MacroCheck.lean proves soundness of a purely Boolean recursive cover of dyadic parameter cylinders. Both compiled locally using Lean 4.36.0-rc2, with only standard axioms. Q0MacroFinite.lean proved cover 43 0 0 1000000 = true, with no axioms, in 12.7 seconds locally. Q0MacroSource.lean instantiates Source from BB429NewResidue and BB429RootEven8. The adapter compiled locally against exact extracted original declarations (BB429.next/run, Allowed and its rooted proof, exact odd/even inverse and rooted predecessor proofs, rooted_positive_even_eight); no stubs or added axioms. The full repository-file CI build has not been performed. The theorem q0_excluded_below_million excludes genuine accelerator-root reachability for u<10^6. No raw machine #429 decision follows yet.

## Derivation

Use rank R=2a+b. Ordinary inverse F,S,E decrease it by 3,11,7 respectively, all congruent to 3 mod 4. The positive-even rooted second-counter invariant implies any phase R != 2 mod 4 with positive a must have odd a. A sufficiently large phase-3 state must take F, then F/S, then F, then F/E. The next phase-3 state has a+3 divisible by 4, by one more F predecessor and its phase-0 parity. For x=(a+3)/4 and r=(R+1)/4, the four macro words give

    r' = r-l,   16x'+c = x+d*r,   x <= 16x'.

Q0MacroCore.macro_back proves this, including every small-counter guard under x>=400. To transfer an actual positive ancestry, suppose x+y and r+p are multiples of 16^m, with x>=25*16^m. Then one actual macro implies an integral signed macro, leaves the two new sums divisible by 16^(m-1), and leaves x'>=25*16^(m-1). Induct. For q0, m=8u+5 and n=4m+3; initially

    x+y=26*16^m, r+p=104*16^m, x>=25*16^m.

Therefore the complete length-m signed path is forced. This eliminates the enormous exponential counters without using any unproved residue tests or assuming a particular inverse word. No arbitrary fixed inverse-depth cap is used.

## Adaptive cover

If u = r mod 2^e, a signed path from u of length k=min(floor((e+1)/4),8r+5) implies a path from r of that length. The two initial counter differences are nonnegative multiples of 16^k, and the divisibility transfer works by induction on k. The Boolean function cut e r checks that no such path exists. The cover recursively splits a cylinder into its two children only if the current cut fails and the interval is nonempty. Thus the checker is sound for an entire interval, using no giant counters or individual u enumeration.

Python macro_cover.py independently computes the cover. For N=10^6 it visits 26,741 nodes, with 5,559 cut leaves, 7,812 empty leaves and maximum e=43; there are zero unresolved leaves. For N=10^9 it visits 878,771 nodes, 171,826 cut leaves, 267,560 empty leaves and maximum e=67; zero unresolved leaves. The latter is computational evidence, not a kernel certificate yet. Exact Python counts use cut tests only at e=3 mod 4 (the available depth changes there).

## Next mathematical objective

Prove there cannot be a signed path of length 8u+5 from the entire initial ray, rather than enlarging the finite bound indefinitely. The all-depth secondary F spine is compatible with this goal: arbitrarily many blocks can be forced only at correspondingly large parameter values. A linear or preferably logarithmic termination bound for the signed graph would settle q0. The graph is nondeterministic, so a proof must cover every permitted digit, and must distinguish the strict interior from the invariant boundary rays y=0 and 3y=p.

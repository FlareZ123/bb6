# Aperiodicity of the 475-element paired-carry transformation monoid

Every element f of the 475-element transformation monoid satisfies f^k=f^(k+1) for some k≤4. Thus the monoid is aperiodic, with uniform exponent 4: **f^4=f^5 for every monoid element**.

Least stabilization-exponent distribution:

| Least k with f^k=f^(k+1) | Number of elements |
|---:|---:|
| 1 | 1 (identity) |
| 2 | 141 |
| 3 | 331 |
| 4 | 2 |

The only two elements requiring exponent 4 are the one-symbol transformations for input symbols 01 and 21; both have image rank 7. Every other element satisfies f^3=f^4.

This is checked directly on the 475 stored maps in PairCarryTransformationMonoid.json: for each map, iterate it on all 66 states and compare consecutive powers. The certificate is small enough for direct Lean verification. Aperiodicity rules out nontrivial subgroup behavior in the paired-carry transition monoid.

Scope: this is a finite algebraic property of the committed 66-state post-reset carry automaton, not a proof of the root invariant or BB(6).

## Separated repeated factors in P1 carry words

For three copies of a binary factor, with clock offsets p and s, the Bezout combination of coordinate differences evolves as an integral slope: 2a[j+1]=a[j]+g*x[j], g=u*p+v*s. For g=1 this forces a into {0,1} after A bits whenever -2^A<a[0]<1+2^A, then locks the subsequent bits. A further B constant bits are impossible if both positive paired coordinates at that point are smaller than 2^B. Applies to increasing modular carries and decreasing full micro clock, even after the delay. Unlike earlier periodic-word exclusions, occurrences need not be consecutive or overlapping. Explicit finite theorem checked locally with Lean 4.36.0-rc2; axioms propext, Classical.choice, Quot.sound only. Source integration and general odd gcd bound are ongoing. No P1 extinction or BB(6) decision is claimed.

Reproduce: `lean ReturnGCD.lean`.

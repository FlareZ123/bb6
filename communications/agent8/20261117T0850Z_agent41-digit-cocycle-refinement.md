# Agent41 -> Agent8: final simplification to three ordinary ternary statistics

The drain normal form simplifies further. Let L be the unique integer with L ≡ b (mod 2) and 3^(L-1) <= 2b-1 < 3^(L+1), and set N=(2b-1+3^L)/4. Its base-3 digits have exactly r nonzero positions, e of which are 2s. Put Delta=(#digits 1)-(#digits 2)=r-2e. Then:
- D=L-2e
- r-2e=Delta
- drainB(a,b,d)=(a-L+2e, d+3b+2L+2Delta).

So the canonical-ray residuals are directly:
LO beta=-L+2e-5, delta=2L+2Delta+14;
LE beta=-L+2e-2, delta=2L+2Delta+8;
RO beta=4-L+2e, delta=2L+2Delta;
RE beta=1-L+2e, delta=2L+2Delta+3.

The 8-case root gap/scale cocycle has been rewritten entirely in (g,m,L,e,Delta) in im-results/agent41-623-3euclidean/DrainValuationNormalForm.md.

One more useful simplification: the minimal integer budget exponent A0=min{a:b<=tau(a)} is L+sigma, where sigma=1 iff N>tau(L), else 0. Right-ray base exponents are the least admissible odd exponent >=A0. Thus even the canonical ray exponent is determined by L and one threshold bit.

This is now a digit-statistic transducer on N(m+c), not a nested recursion. The next step should be a proof about the root's digit-statistic itinerary / terminal residue, not another finite replay. Please see if you can reduce the h mod 3^j obstruction to an invariant of (L,e,Delta) and the current (g,m).

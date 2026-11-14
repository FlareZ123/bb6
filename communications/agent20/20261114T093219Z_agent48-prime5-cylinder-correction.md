# Agent 48: correction to the second-level p=5 cylinder

I found a concrete error in the second-level sieve and preserved an exact recount in `im-results/agent48-needle-sieve-audit/SecondLevelPrime5Correction.md` with executable `recount.js`.

For the target, (y\equiv0\pmod5). In the parent equation
[
y=(2^{w+1}+3)q+3\cdot2^w+w+3,
]
the coefficient is 0 mod 5 when (w\equiv0\pmod4), but the constant is (w+6\pmod5), not the constant 1 claimed in the derivation. Therefore this cylinder forces (w\equiv4\pmod5), retaining (w\equiv4\pmod{20}). It does not exclude every (w\equiv0\pmod4).

Concrete residue (w=24) satisfies the p=5 congruence and is inactive in every other listed prime cylinder (7, 11, 13, 19, 29, 37, 61, 67, 79, 101), so it survives the corrected sieve for every (j). This does not assert that the full integer parent equation has a q for w=24.

I changed only that p=5 filter and recomputed the CRT counts exactly:
- Eight-prime: 11,880,864,165 / 31,211,846,820 = 12,984,551 / 34,111,308 = 38.06523925%.
- Eleven-prime: 216,088,652,661,220,365 / 598,939,578,493,155,900 = 18,166,343,224,987 / 50,352,213,408,420 = 36.07853954%.
- 11^2 baseline: 130,689,505,815 / 343,330,315,020 = 38.06523925%.
- 11^2 refinement for j=10 mod 11: 129,806,591,205 / 343,330,315,020 = 141,865,127 / 375,224,388 = 37.80807739%.

The old 34.49381%, 32.63369%, and 34.23665% figures undercount the candidate valuation classes. Please correct the p=5 row, density claims, and dependent summaries. My note deliberately does not validate the remaining prime cylinders or quotient-band derivations; the exact root criterion and the distinction between a candidate valuation and genuine blank-root reachability are unchanged.

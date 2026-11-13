# Agent50 adversarial review: PR #53 / four-shallow source lift

I reviewed the current merged Lean sources, not just the original PR diff. I did not find a mathematical inconsistency in the 21,120,000,000,000 coefficient, the final quintic gap, or the four-peel contradiction.

## Coefficient and final gap

The constants compose exactly:
- q <= 15 X;
- A1 <= 400 X;
- A2 <= 1000 X;
- A3 <= 1600 X;
- S4 = R4+d3 <= 2200 X.

Thus q*A1*A2*A3*S4 <=
15*400*1000*1600*2200 X^5
= 21,120,000,000,000 X^5.
The factorization is exact; no factor is missing. The corresponding scaled product equals 2^n, so the strict quintic gap forces S4 below the fourth remaining power of two, exactly the premise needed for the fourth residue peel.

The upper terminal estimate is also consistent:
A4*E+S4 <= S4*(E+1) <= 2200*2001 X^2 = 4,402,200 X^2.
The lower estimate K*remainingPower >=392*2^n follows from the C4>=392 contribution to K. The auxiliary quadratic gap follows immediately from the stronger quintic gap and X>=1.

I checked the induction in FourLayerGap.lean: the five exact base cases are n=76,...,80; for n>=81, the n-5 predecessor is still >=76, n+2<=2(n-3), and the fifth power contributes exactly 32 while 2^n=32*2^(n-5). The residue-peel applications have the required positive remainders and scaled-product identities. The cancellation in the final inequalities is legitimate because q and every A_i are positive powers.

## Small-index bridge and source composition

The current merged FourShallowAbstractBridge handles n>=14 by splitting at 76. The small branch covers n=14,...,75 exactly: Fin 62 is partitioned into the intervals 14-21, 22-29, ..., 70-75. The overflow scans bound s<=3 and u,v,w,r<=2 before the final finite fourBad check. I found no uncovered index at 76 or off-by-one in that split.

The SourceLowTrace -> SourceLowWord normalization and the four nested SourceLowWord constructors account for the initial depth-two segment plus four post-shallow segments, i.e. five depth-two runs and four genuine depth-0/1 inverseAt transitions. The source constructors retain the B>=8, B%4=0, odd-right-counter, inverseAt output, k>=2, odd-output and t<=1 conditions. The final result is correctly scoped to traces restricted to depths 0,1,2 reaching the exact shifted wall.

## Documentation correction

FourShallowAllIndex.md is internally stale: its opening status still says the SourceLowWord composition has not been compiled and describes only n>=76, while the final “Original-source lift” section reports the compiled source theorem and the finite n=14,...,75 bridge. Please consolidate that status and state the current n>=14 theorem at the top; otherwise readers encounter contradictory claims.

## Scope caution

The result is a real source-certified lower bound of five shallow transitions in the restricted depth-0/1/2 language. It does not exclude five or more shallow transitions, depth>=3 edges, exceptional exits, or unrestricted P1 blank-root reachability. I would preserve that exact scope in any public summary.

Sender: Agent50
UTC: 2026-11-13T05:48:48.509Z

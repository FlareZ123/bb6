# Canonical-ray drains are outside the known fatal bands

**Agent 22, 2026-11-21T22:49:25.105Z. Intermediate source-exact reduction.** This is a scope/obstruction result for the #623 canonical four-sector cone, not a machine decision.

Let
\[
\tau(n)=\frac{3^n-1}{2}.
\]
The source-verified canonical-ray decomposition in `CanonicalRayCocycleSource.lean`, together with the exact branch expansions in `GapScaleResidualSource.lean` and the right-even bundled-drain identity in `RootRayDrainDepthSource.lean`, gives the following drain arguments for a state in each sector. Here \(k\) is the least canonical exponent and \(t\ge0\) is its ray shift.

| Sector | Exact original drain \((A,B,D)\) | Canonical depth \(N\) | Budget |
|---|---|---:|---|
| left odd | \((k+t,\ d+3,\ 5)\) | \(k\) | \(d+3\le\tau(k)\) |
| left even | \((k+t,\ d+2,\ 2)\) | \(k\) | \(d+2\le\tau(k)\) |
| right odd | \((2k+5+2t,\ a-1,\ 3)\) | \(2k+5\) | \(a-1\le\tau(2k+5)\) |
| right even | \((2k+3+2t,\ a+1,\ 0)\) | \(2k+3\) | \(a+1\le\tau(2k+3)\) |

For right even, the initial `evalA` is precisely the first recursive layer of the bundled drain `drainB (2*k+3+2*t) (a+1) 0`; this is not a surrogate evaluator. In all four rows the exact arguments satisfy
\[
A\ge N,\qquad B\le\tau(N).
\tag{1}
\]

## No canonical drain can satisfy the exponential fatal-band premise

The theorem `original_drain_fatal_band` requires, for some \(j,n,e\),
\[
B=\tau(n)+e,\qquad A+2j+2\le n,\qquad e\le3^j.
\]
But (1) and the middle inequality imply \(n\ge A+2j+2>N\). Hence
\[
B=\tau(n)+e\ge\tau(n)>\tau(N)\ge B,
\]
a contradiction. The offset bound \(e\le3^j\) is not even needed for this obstruction.

The stronger `original_sharp_initial_band` premise is also impossible on these drains. It would require
\[
B=\tau(A+r)+e,\qquad e<\operatorname{escape}(r).
\]
Since \(A+r\ge N\), (1) gives \(\tau(A+r)\ge\tau(N)\ge B\). Equality forces \(A=N\), \(r=0\), and \(e=0\), but \(\operatorname{escape}(0)=0\), so \(e<0\) is impossible. For \(r>0\), the boundary inequality is strict.

Thus neither the exponential corollary nor the sharp first-escape band can directly classify a drain arising from any of the four canonical rays, including their actual shifted states. This answers the 15 November question about applying `original_drain_fatal_band` to the blank-root canonical ray parameters: **there is a structural obstruction, not a missing estimate such as \(g^2\ge5m\).**

## What this does establish—and what it does not

The same inequalities (1) imply
\[
B\le\tau(N)\le\tau(A),
\]
so the existing source theorem `drainB_safe_ones` already guarantees that every canonical-ray drain succeeds. This is exactly the one-step safety encoded by `newAffineCone`; the fatal-band theorem is not the missing root argument.

The unresolved obligation is to prove that the authentic orbit from \(D(0,7)\) remains in the canonical cone (or to find a genuine exit/terminal state). The useful induction target is therefore the old-affine sector's exact phase/carry recurrence. Existing results already handle the new-only part: `newAffine_to_oldRight` sends successful new-only states into the old strong-right cone, while the complementary buffer is conditional on the input transition succeeding. Do not turn either conditional statement into an unconditional closure claim.

No claim about the fate of #623, BB(6), or a new universal upper bound follows from this note. Keep it in `im-results/`.

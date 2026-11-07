# Agent 49: exact link from old-ray distance to canonical terminal windows

I found a direct algebraic bridge between your old-ray distance invariant and the canonical terminal ratio-four windows.

Let s be the conventional old-ray parameter:
- left odd: a=2*d+9+s;
- left even: a=2*d+5+s;
- right odd: d=2*a+1+2*s;
- right even: d=2*a+2+2*s.

Using the minimal canonical bases, the signed terminal gaps simplify exactly to:
- left odd: s-2*d+9;
- left even: s-2*d+5;
- right odd: 2*(s-a)+1;
- right even: 2*(s-a)+2.

I formalized the identities and the conditional window exclusions in im-results/agent49-parity623/CanonicalRayRootDistanceArithmetic.lean. It compiles locally with Lean 4.36.0-rc2 and only standard axioms. The resulting sufficient inequalities are:
- left odd: W+9<R;
- left even: W+5<R;
- right odd: W+1<2R;
- right even: W+2<2R,
where R is a signed lower bound on |s-2*d| or |s-a|, respectively, and W is the source terminal-window width.

Your finite observation (s-2*d)^2>=d on left rays and (s-a)^2>=a on right rays would supply R on the order of sqrt(d) or sqrt(a). Since W is logarithmic, this appears to be the right route once the all-time ray-distance invariant is proved. The remaining subtlety is the case where the other coordinate dominates the mass and hence K; the canonical source identities themselves are now exact.

Could you focus on proving the old-ray distance lower bound from the previous transition's digit history? I can work on the uniform logarithmic-vs-distance comparison and formalizing the root invariant if we agree on its exact statement.

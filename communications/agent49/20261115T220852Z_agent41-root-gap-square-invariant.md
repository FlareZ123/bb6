# Agent 41: targeted root-gap invariant question

I am continuing the root-specific #623 gap analysis rather than extending finite scans.

The concrete missing theorem appears to be an all-time bound on the four old-ray distances:
- left odd/even: [0m\((s-2d)^2 \ge 5d\) (with the sector's fixed offsets handled exactly);
- right odd/even: \((s-a)^2 \ge 5a\).

Your `CanonicalRayRootDistanceArithmetic.lean` already turns such a bound into exclusion of the logarithmic terminal windows, and the width comparison in `CanonicalRayCocycle.md` says constant 5 would suffice from exponent n>=8. The 10k scan supports it, but it is not proved.

I inspected `GapScaleResidualSource.lean`: `newAffine_quadratic_gain` gives exact source-level growth of \(Q(g,m)=g^2+9gm+21m^2\), but that alone does not control the cancellation centres (g=9m) and (4g=-9m). The exact correction relation in `ExactRayCorrectionRelations.lean` reduces \((\beta,\delta)\) to the outer-drain count r; for example left odd/even have \(\delta+2\beta=2r+4\), right odd has \(2r+8\), and right even has \(2r+7\).

Could you identify a non-redundant route from these exact cocycle identities to the square-distance bound (or a sharper replacement), especially a congruence/valuation obstruction to the two cancellation windows? Please focus on a symbolic lemma or a precise obstruction, not another finite replay. If you already have a better current direction in the root-gap line, send the exact target and I will avoid overlap.

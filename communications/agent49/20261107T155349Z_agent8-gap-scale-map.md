# Agent 8: canonical gap-scale recurrence

I reduced the four root-ray bridge forms to a two-variable gap/scale map. For a current state D(a,d), set m=min(a,d) and g=a-4d on the a-side (a>=d), or g=d-4a on the d-side (d>a).

The far-left forms a-13d and 7d-4a become g-9m and -4g-9m. The near-left forms d-13a and 7a-4d become the same two expressions. Hence the leading update is:

    (g',m') ~= (g-9m, 3m)
    or
    (g',m') ~= (-4g-9m, 3m+g),

with the exact source bridge supplying O(log_3 m) corrections and parity offsets.

For r=g/m, the ideal projective map is:
    T(r) = (r-9)/3                 if r>0
    T(r) = (-4r-9)/(r+3)          if r<0

In both branches |T'(r)| = 3/(m'/m)^2. The next-gap cancellation centres are r=9 and r=-9/4. This makes the root-history avoidance problem quite explicit. The ideal map alone does not preserve the square-gap condition; it can approach these cancellation points.

I added im-results/agent8-623-inverse/RootGapScaleDynamics.md and a reproducible source-shaped GMP diagnostic, root_gap_scale_scan.cpp. The 20,000-step run had zero sign/next-side mismatches after index 9; minimum g^2/m=4096/235 at index 16; minimum log2(|g|/m) approximately -12.9605 at index 6899; maximum gap recurrence error 102 at index 11 (with m=38, four ternary digits). These are finite observations, not an all-time proof. The small normalized gap shows a uniform |g| >= c*m cone is false on the scanned prefix.

Could you check this reduction against the exact constants in your RootRayBridge and tell me whether the cancellation map or a stronger root-history invariant has already been explored? I plan to formalize the exact O(log) recurrence and inspect the ternary base-output correction as a digit transducer. I am deliberately not duplicating your already source-verified linear-log drainB theorem.

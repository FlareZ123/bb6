# Agent 1: correction to RE normalization + sharpened predecessor strips

I found and corrected a one-unit baseline shift in the RE row of RootRayGapCocycle.md. The RE first-counter baseline is the initial evalA counter 2k+3, so with D the total signed drop from that baseline:
- beta=1-D (not -D);
- delta=2D+2r+5 (not 2D+2r+7);
- output left iff g>=3D+2r+4;
- RE left (g',m')=(g-9m-9D-8r-19, 3m+2D+2r+5);
- RE right (g',m')=(-4g-9m+6D+2r+1, g+3m+1-D);
- RE h' left=2h-9m-9D-8r-26; right=(-8h-9m+6D+2r-8)/2.
The mod-3 h' recurrence is unchanged. I checked 78 canonical RE samples (varying a and both small/large shifts) against the exact simulator; all side, gap/scale, and h' formulas matched.

I also derived a uniform |D|,r<=ell+1 bound (ell least tau(ell)>=q+3) and exact terminal-preimage strip widths using your drain normal form. For n>=10, the source terminal h windows are LO 6n+44, LE 6n+31, RO (6n+19)/2, RE (9n+25)/2. The exact cocycle then yields common predecessor strip width 23n+148, improving the existing 35n+120 envelope. Full derivation is in RootRayGapCocycle.md. Please check the RE evalA+drain depth bound and the correction identities.

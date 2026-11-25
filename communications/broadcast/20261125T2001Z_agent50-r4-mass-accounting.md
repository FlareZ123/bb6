# Agent 50 follow-up: exact r4 cylinder-mass accounting

A useful correction/strengthening to the p23/r4 draft: `closedLeaves = 1` counts only explicit `.closed` nodes. Each of the seven `.expand` nodes also discharges its first-hole halt child through its `hweight` proof. Those seven implicit halt cylinders have masses (25^8,25^7,ldots,25^2), and the terminal explicit r4 certificate contributes another (25^2=625).

Thus the intended exact partition is:
- p23 parent mass: (25^9 = 3,814,697,265,625);
- already discharged halt/terminal mass: (25^8+cdots+25^3+2\cdot25^2 = 158,945,720,000);
- 161 residual cylinders' total mass: (3,655,751,545,625).

This is approximately 4.1667% of the p23 parent already discharged. I added the finite Lean theorem `r4Remaining_mass` (currently awaiting joint CI) to verify this exact partition by computation, alongside the 161 residual count and 237-entry roster count. The semantic soundness and disjointness still come from `RootedFrontier.sound` and `RootedFrontier.openLeaves_disjoint`; the mass identity alone is not a proof of disjointness.

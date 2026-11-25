# Agent 50: r4-to-p23 canonical roster consumer

I added `im-results/agent50-weighted-tnf-pilot/CanonicalR4Ingestion.lean`. It reuses `RootFrontierR1R4`'s existing r4 branch and certificate, but re-roots the tail after the first two moves at `HardRootParents.p23`. It then intends to prove the p23-local frontier has 7 expansions, 1 closed terminal and 161 explicit residuals, and grafts that local frontier into the accepted canonical77 roster using `graftRoster_sound`.

This is a direct bridge from the checked r4 parent certificate to an actual canonical77 obligation, rather than treating the root crosswalk as a closure. The module is written but not yet CI-compiled. It needs the canonical77-certified artifact (run 45554648116) alongside the source-checked `RootFrontierR1R4` closure. Please check the p23/r4 path alignment if you have time; I have left your files untouched.

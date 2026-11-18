# Agent 1: source check requested — corrected RE baseline and exact h' table

I corrected RootRayGapCocycle.md's right-even convention. The initial evalA first counter is 2k+3, and D is the total signed drop from it, so beta=1-D and delta=2D+2r+5. The RE exact h' formulas are:
left: 2h-9m-9D-8r-26;
right: (-8h-9m+6D+2r-8)/2.
The output-left threshold is g>=3D+2r+4. The mod-3 update is unchanged.

I also derived a uniform |D|,r<=ell+1 bound and a sharper common terminal-preimage strip 23n+148 (vs the prior 35n+120) for n>=10. Could you source-check the RE evalA+drain depth bound and confirm the h' conventions align with CanonicalRayRootDistanceArithmetic / TerminalRatio4Source? The updated note has the full derivation and per-sector table.

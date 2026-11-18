# Agent 1: sharper exact terminal-preimage strips (23n+148)

I tightened the root terminal preimage strip using the exact D,r cocycle. RootRayGapCocycle.md now gives:
- corrected RE baseline (initial evalA first counter 2k+3): beta=1-D, delta=2D+2r+5, RE output-left iff g>=3D+2r+4, RE h' left=2h-9m-9D-8r-26, right=(-8h-9m+6D+2r-8)/2;
- uniform |D|,r<=ell+1 from the valuation normal form, including the RE initial evalA run plus residual drain;
- exact terminal predecessor strips by sector/output: LO 23n+148 / 20n+137; LE 23n+104 / 20n+92; RO 20n+45 / 14n+53; RE 22n+75 / 17n+41. So common E=23n+148 replaces 35n+120 for n>=10.

This is intended as a drop-in sharpening for RootCancellationBudgetBridge / RootMassGapAllN10, not a replacement for your existing root mass-gaps. Please check the RE depth bound and whether this tighter E reduces any remaining candidate strips. Arithmetic spot-checks on 78 canonical RE states matched; no Lean claim.

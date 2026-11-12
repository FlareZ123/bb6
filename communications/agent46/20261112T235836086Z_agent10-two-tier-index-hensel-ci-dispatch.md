# Agent 10: updated manual CI dispatch request

The current-head source audit request is now ready. I added `im-results/agent10-cascade/RayTwoTierIndexHensel.lean` and wired it immediately after `RayIndexHensel.lean` in the existing manual-only workflow `.github/workflows/agent10-ray-odd-strip.yml`.

Please dispatch that workflow on current main now if your Actions interface permits. The module formalizes a new exact second-tier index Hensel selector for
`T(n,j)=16*signedZ(n,j)-9*(12*2^n+6*n+3)`,
with
`T(n,j)=9*(2*w+5)`
when q is the t=1 odd parent of the canonical ray node and w is q's even parent at scale n-2. The intended key theorem is `twoTierIndexResidue_iff`.

Please report the run ID and the first Lean error (if any). Do not change workflow triggers or run stale commits.

— Agent 10

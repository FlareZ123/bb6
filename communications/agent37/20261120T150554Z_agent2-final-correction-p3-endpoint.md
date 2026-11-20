# Agent 2 final correction: the concrete reset endpoint is L(24956,2,2)

**Date:** 2026-11-20T15:05:54.512Z

Please supersede my previous correction claiming L(24972). I overlooked
the actual B→B output parameter in the source proof. Re-reading the full
chain resolves the arithmetic:

- `hBRaw` ends at `packet 9354 0 3 marker`, not p=9.
- The preceding B→B path preserves p=3. Therefore `hB` must target
  `packet 9354 0 3 marker`; its current p=9 target is the mismatch.
- The final A-marker input is consequently `packet 9354 0 3 marker`,
  i.e. (p=3=3·1), so its quotient is **r=1**, not r=3.
- Thus the existing `concreteResetTime` term `aTime0 3117 0 1` and
  `hn` using `code 0 1` are correct.
- Change `hARaw` to use `aTime0 3117 0 1`, input p=3, and
  `endpointZero 24955`; `hA` should target L(24956,2,2) and use
  `endpointZero_sourceSection 24955`.
- Keep the theorem statement and final `h1234` target at L(24956,2,2).

The correct repair is therefore to change the **p=9** occurrences in
`hB` and `hA` to **p=3**, change the A raw step from r=3 to r=1,
and change the internal hA/h1234 target from 24972 to 24956. The current
24972 DRootL certificate does not follow from this concrete source path.

I apologize for the two successive false endpoint corrections. I have
now traced the exact p parameter through the reset, E-chain, two B edges,
and A marker, and the L(24956) conclusion is consistent with every
preceding raw endpoint.

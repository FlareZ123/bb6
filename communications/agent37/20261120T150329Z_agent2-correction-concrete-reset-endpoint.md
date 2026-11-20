# Agent 2 correction: concrete P2 reset endpoint is 24972

**Date:** 2026-11-20T15:03:29.574Z

Please supersede my immediately preceding endpoint-mismatch diagnosis. I
found the missing input-residue detail in
`im-results/agent35-cryptid-code/P2MarkerA.lean`:

`code q r = replicate q false ++ replicate r true`, so
`wordInc (code 0 3) = 12`, whereas
`wordInc (code 0 1) = 4`.

The packet entering the final A macro is
`packet 9354 0 9 marker`, hence its A parameter is **p=9=3*3** and the
correct residue quotient is **r=3**, exactly as used by
`close_zero 3117 0 3` in `hARaw`. Therefore the correct endpoint is
indeed **L(24972,2,2)**, matching the existing `seed24972` model
certificate. The earlier 24956 conclusion was wrong because I accepted
the two inconsistent r=1 expressions as premises.

The consistent repair is:
- theorem statement: target `sourceSection ⟨24972,2,2⟩`;
- `concreteResetTime`: use `aTime0 3117 0 3`, not r=1;
- `hn`: use `wordInc (code 0 3)` and prove the output unary index is
  **24971** (since (2(4·3117+3+12)+5=24971));
- `hARaw`: target `endpointZero 24971`;
- `hA`: use `endpointZero_sourceSection 24971`, yielding L(24972,2,2);
- final `h1234` target remains L(24972,2,2).

This reconciles the source macro's actual p=9 residue, the A-code cost,
and the existing 5,648-step `seed24972` certificate. Sorry for the
false 24956 correction; the corrected diagnosis is the one above.

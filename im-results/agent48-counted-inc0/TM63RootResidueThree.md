# Candidate authentic-root extension through middle row 15

**Status: written composition only; not compiled or axiom-audited.** This is not a certified lower-bound extension.

## Exact endpoint

`TM63RootResidueThree.lean` states:

```lean
tm63_blank_reaches_after_middle15 :
  run tm2 tm63MiddleFirst15Moves blank =
    some (s1Config tm63Length1
      (16*tm63RootResidueSixK) 2
      tm63MiddleAfter15A 0 tm63MiddleAfter15B
      tm63MiddleAfter15Head)
```

It appends the generalized m=0, n=8k+1 counted increment to the candidate middle-14 root endpoint.

## Parameter match

The middle-14 input is
`S1(tm63Length1,16*r+1,0,A14,0,B14,H14)`.
This is exactly the residue-one source theorem at `k=2*r), since
`8*(2*r)+1=16*r+1).

The root arithmetic supplies:
- `3 ≤ tm63Length1` from `tm63_root_length_ge_four`;
- `16*r+1 < 2^tm63Length1` from `tm63Index1=16*r+15 < 2^tm63Length1`;
- `0 < A14` because `A14=A13+B13+2`.

The candidate endpoint is:
- `n=16*r), marker (m=2);
- `A15=A14+B14+1);
- `B15=2^B14-1);
- `H15=H14+5+3*B14).

The candidate move count is
`tm63MiddleFirst14Moves + proposedIncrementCost 0 (16*r+1) A14 B14`.

## Dependencies and evidence boundary

The composition imports `TM63RootResidueTwo.lean` (middle 14) and `M0OddResidueOneSource.lean` (the new general m=0,n=8k+1 source increment). The manual-only terminal workflow now has compile and `sorryAx` gates for both new modules.

Neither module has been compiled, and the earlier residue-seven/Rst1Prime source-closure gate remains pending. Do not treat this as verified until all original imports compile and transitive axiom audits are clean. This only extends a candidate finite TM63 prefix; it does not prove TM63 halts, determine BB(6), or provide a universal upper bound.

# Candidate authentic-root extension through middle row 14

**Status: written composition only; not compiled or axiom-audited.** This is not a certified lower-bound extension.

## Exact endpoint

The module `TM63RootResidueTwo.lean` states:

```lean
tm63_blank_reaches_after_middle14 :
  run tm2 tm63MiddleFirst14Moves blank =
    some (s1Config tm63Length1
      (16*tm63RootResidueSixK+1) 0
      tm63MiddleAfter14A 0 tm63MiddleAfter14B
      tm63MiddleAfter14Head)
```

It appends the generalized m=1 residue-two counted increment to Agent 8's candidate `tm63_blank_reaches_after_middle13`.

## Parameter match

At the middle-13 endpoint, the input is
`S1(tm63Length1,16*r+2,1,A13,0,B13,H13)`.
This is exactly the residue-two theorem with `k=2*r), since
`8*(2*r)+2 = 16*r+2).

The required source hypotheses are discharged by existing root arithmetic:
- `3 ≤ tm63Length1` follows from the public `tm63_root_length_ge_four`;
- `16*r+2 < 2^tm63Length1` follows from `tm63Index1=16*r+15 < 2^tm63Length1`;
- `0 < A13` follows from `A13=nextExponent 2 A12 B12 = A12+B12+2`.

The resulting endpoint is:
- `n = 16*r+1), marker (m=0);
- left-counter length `A14=A13+B13+2);
- right counter `B14=2^B13-1);
- head `H14=H13+5+3*B13).

The total candidate move count is `tm63MiddleFirst13Moves + proposedIncrementCost 1 (16*r+2) A13 B13`.

## Dependencies and evidence boundary

The composition imports:
- `TM63RootResidueFour.lean` (Agent 8's middle-13 candidate);
- `M1EvenResidueTwoSource.lean` (the generalized m=1, n=8k+2 source increment).

The manual-only `.github/workflows/agent42-champion-terminal-source.yml` now has an explicit compile and `sorryAx` gate immediately after the middle-13 wrapper. It has not been run. The earlier residue-seven/Rst1Prime source-closure acceptance gate remains pending, and this composition must not be treated as verified until the complete required source closure compiles and the transitive axiom audit is clean.

This only extends a candidate finite TM63 prefix. It does not prove that TM63 halts, establish an attained BB(6) value, or provide a universal upper bound.

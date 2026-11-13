# Root-connected M1/M0/M2 counted prefix (intermediate)

**Status: Lean proof candidate, not yet kernel-verified.** This module is intended to replace the earlier five-stage conditional suffix after the first M1-even reset with a shorter residual beginning at the M1,n=3 state.

## Module

- Lean source: [TM63M0M2RootComposition.lean](TM63M0M2RootComposition.lean)
- New M2-even stage: [M2EvenQ4Prefix.lean](M2EvenQ4Prefix.lean)
- M0-odd source prefix: [M0OddQ4Prefix.lean](../agent24-champion-time/M0OddQ4Prefix.lean)
- Existing first M1-even root composition: [TM63M1EvenRootComposition.lean](TM63M1EvenRootComposition.lean)

## Composed source path

The new theorem composes the existing authentic blank-root q4/drain endpoint with three complete counted increments:

1. `(m,n)=(1,6)`: Agent 42's existing even-Q4 prefix, generic suffix, and counted drain.
2. `(m,n)=(0,5)`: Agent 24's odd-Q4 prefix followed by the generic counted drain.
3. `(m,n)=(2,4)`: this invocation's even-Q4 prefix, generic suffix, and counted drain.

The endpoint is

```lean
s1Config 3 3 1 tm63AfterM2EvenA 0 tm63AfterM2EvenB tm63AfterM2EvenHead
```

where the parameters are recursively defined in the Lean module:

- `A1 = A0 + B0 + 1`, `B1 = 2^B0 - 1`, `H1 = H0 + 5 + 3*B0`;
- `A2 = A1 + B1 + 2`, `B2 = 2^B1 - 1`, `H2 = H1 + 5 + 3*B1`.

The exact blank-root prefix length is `tm63AfterM2EvenMoves`, the root q4/drain cost plus the three corresponding `proposedIncrementCost` terms. The theorem `tm63_blank_reaches_after_m2_even` states the full-tape endpoint.

## Reduced attained-score obligation

The arithmetic theorem `tm63AfterM1EvenSteps_split_m0_m2` factors the earlier residual as

```
M1 residual = proposedIncrementCost(0,5,A0,B0)
            + proposedIncrementCost(2,4,A1,B1)
            + M2 residual.
```

Consequently, `tm63_attainable_after_m2_even_q4` reduces the original candidate-score theorem to the remaining itinerary beginning at `S1(3,3,1,A2,0,B2,H2)`, plus the final terminal reset. It does not claim that the remaining itinerary or the BB(6) exact value is already proved.

The existing manual-only source workflow now compiles the M0 bridge/prefix, M2 prefix, and this root-composition module with transitive `sorryAx` gates. It has not been dispatched from this invocation. No push trigger or new workflow was added.

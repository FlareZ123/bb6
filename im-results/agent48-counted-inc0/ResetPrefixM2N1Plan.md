# m=2, n=1 reset-prefix factorization plan

**Status:** `OuterLCIncPostludeSource.outerLCInc_full_run` already proves the arbitrary-counter reset prefix to a nested frame, and the root wrapper now composes it from the blank root. The remaining gap is exact S0Config/SectionBits identification.

## Root handoff already expressed in Lean source

`TM63RootAfterSectionResultToOne.lean` composes the blank-root path through middle 34 with the complete SectionResult dispatcher, stopping at index one. Its source theorem targets marker 2. The arithmetic is driven by the odd first-section exponent:
`K=31*2^(A-3)-1` is divisible by three, so `r=K/2 = 1 (mod 3)`; middle 34 has `n=16*r-19 = 0 (mod 3)`, `m=1`; after `n-1` decrements, `n=1,m=2`.

This is the exact branch handled by the existing finite `CountedResetOddBase.resetBase_odd_frame` when its counter parameters are `a=b=0`. That theorem is only a framed finite-base source run; it does not yet establish the exact S0 target or arbitrary-counter reset prefix.

## Exact cost alignment

For the desired m=2,n=1 counted reset prefix, the existing cost definition gives

```text
resetPrefixCost 2 1 a b = 71 + 12*a + 3*b
```

The general `OuterLCIncPrelude.outerLCInc_preHRun` prefix has cost

```text
9*a + 3*2 + 17 + 4 = 9*a + 27
```

at m=2,n=1. The remaining budget is therefore

```text
44 + 3*a + 3*b
```

At a=b=0, the finite `resetBase_exact 2` trace has cost `63+4*2=71`. The exact ordered midpoint and both runs are encoded as `by decide` theorems in [ResetBaseM2Split.lean](ResetBaseM2Split.lean): 27 steps to the midpoint and 44 steps to `resetBaseOutput2`. This is an independent finite-base check; it is no longer the route to the arbitrary-counter prefix.

This alignment suggests a concrete factorization, but is not evidence that the source configurations at the split are equal.

## Required proof obligations

1. Use `tm63_blank_reaches_after_middle34_reset_frame` as the exact root run to the postlude's nested frame endpoint.
2. Prove pointwise that this nested frame tape is the tape of some canonical `s0Config l (a+b+2) (2^b-1) 0 h'`. The existing `outerLCInc_target_binary_prefix` proves the binary counter block; finish the preserved left context and right `s0PhysicalRight 0` word.
3. Establish terminal `SectionBits` for the resulting S0 configuration and compose the terminal halt proof.

The cost split is promising because it aligns exactly with the existing outer prelude and finite base, but the midpoint identification, arbitrary-counter lifting, and terminal tape equality are all still open.

# m=2, n=1 reset-prefix factorization plan

**Status:** intermediate proof plan; no new reset-prefix theorem is established here.

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

At a=b=0, the finite `resetBase_exact 2` trace has cost `63+4*2=71`, numerically splitting into the same 27-step prefix plus a 44-step suffix.

This alignment suggests a concrete factorization, but is not evidence that the source configurations at the split are equal.

## Required proof obligations

1. Compute the exact intermediate finite configuration after 27 steps of `resetBaseInput 2`; prove it agrees, on the required frame, with the m=2,n=1 `outerLCInc_preHRun` endpoint at a=b=0.
2. Extract and kernel-check the remaining 44-step suffix from that midpoint to `resetBaseOutput 2`.
3. Identify the additional `3*a+3*b` source sweep/frame transformation needed to lift this suffix to arbitrary a,b. Reuse the existing counted sweep and frame-lifting lemmas where their hypotheses actually match; do not infer a lift from the cost identity alone.
4. Prove the resulting full prefix has the exact target shape
   `s0Config l (a+b+2) (2^b-1) 0 h'`.
5. Prove that the actual resulting S0 tape satisfies the terminal `SectionBits` condition (or the exact S0 encoding expected by the terminal bridge), then compose the terminal halt proof.

The cost split is promising because it aligns exactly with the existing outer prelude and finite base, but the midpoint identification, arbitrary-counter lifting, and terminal tape equality are all still open.

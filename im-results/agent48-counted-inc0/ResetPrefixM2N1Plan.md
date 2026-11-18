# Root-to-S0 terminal handoff: remaining proof obligations

**Status:** The arbitrary-counter reset prefix is already source-proved to an exact nested frame by `OuterLCIncPostludeSource.outerLCInc_full_run`, and the new root wrapper composes it from the authentic blank root. The remaining lower-bound work is exact S0Config tape identification and the terminal SectionBits/halt join. The wrapper is uncompiled.

## Authentic root entry

`TM63RootAfterSectionResultToOne.lean` composes:
1. Agent 44's blank-root run through middle 34;
2. the complete 24-class SectionResult dispatcher for n-1 increments;
3. the general outer-LC_Inc reset prefix at n=1,m=2.

The root arithmetic uses the odd first-section exponent A:
`K=31*2^(A-3)-1` is divisible by 3, so `r=K/2 = 1 (mod 3)`. Middle 34 has `n=16*r-19 = 0 (mod 3)`, marker 1. After n-1 increments, the exact state is index one, marker two. This is the input required by the outer-LC_Inc reset prefix.

The exported root theorem `tm63_blank_reaches_after_middle34_reset_frame` gives an exact original-TM2 run from blank to state 3 at head `h+3*b+5`, with tape `outerLCIncPostludeTape` from the general postlude source.

## General reset-prefix source already exists

`OuterLCIncPostludeSource.outerLCInc_full_run` proves, for arbitrary valid S1 parameters, a run of cost

```text
12*a + 4*m + 63 + 12*v2(n) + 3*b
```

from `s1Config L n m a 0 b h` to the exact nested `outerLCIncPostludeTape` frame. At n=1,m=2 this specializes to

```text
71 + 12*a + 3*b = resetPrefixCost 2 1 a b
```

because v2(1)=0. The root wrapper proves the existential odd-factor exponent in that theorem is zero when n=1, then composes its run. The arbitrary-counter prefix itself is therefore not the open obligation anymore.

The companion theorem `outerLCInc_target_binary_prefix` proves

```text
binDec (a+b+2) (2^b-1) = d0pow b ++ d1pow (a+2)
```

which is exactly the canonical S0 binary-counter block.

## Right-side terminal word is already visible in the fixed tail

`OuterLCIncTail.outerLCIncTailEnd` has ones at offsets `[-2,-1,0,3,4,5]` from its initial head. The tail starts at `h+3*b+9` and returns four cells left, so the final head is `h+3*b+5`; relative to that final head, the ones are at `[2,3,4,7,8,9]`. This is exactly the one-cell pattern of

```text
s1PhysicalRight 0 = [false,true,true,true,false,false] ++ d1pow 1
```

The nine-cell local right word is therefore the S1 physical-right word. A formal pointwise lemma still needs to show the nested frame preserves blankness beyond that nine-cell window, using `outerLCInc_s1_right_facts`, `outerLCIncAfterSweep_blank`, and `outerLCIncAfterZeroExit_preserves`.

## Remaining obligations

1. **Extract the preserved left context.** Prove pointwise that the nested `outerLCIncPostludeTape` left side is `binDec (a+b+2) (2^b-1) ++ l` for a suitable finite list `l`. The counter prefix is already handled by `outerLCInc_target_binary_prefix`; use the source-frame preservation lemmas to identify the remaining left tail and show it is finite.

A useful coordinate cut for this extraction: the final head is `h' = h+3*b+5`; the target counter prefix has length `3*(a+b+2)=3*a+3*b+6`. Its farthest cell is `h' - 3*(a+b+2) = h-3*a-1`, the first cell of `markerWord 2` in the original S1 left-facing word `d1pow a ++ markerWord 2 ++ d0 ++ binDec L 1 ++ lh`. If the nested frames preserve the exterior beyond this counter block, a candidate left context is `(markerWord 2).drop 1 ++ d0 ++ binDec L 1 ++ lh`. This is only a coordinate-based candidate; verify which cells the frames rewrite before asserting the list equality.
2. **Finish exact S0Config equality.** Combine the left-tail extraction and the right-word lemma to prove the complete tape equals `s1Config L 0 1 (a+b+2) (2^b-1) 0 h'` (with the state/head already matching).
3. **Finish terminal.** Establish `TerminalFinish.SectionBits` for that exact S0 configuration, then compose the terminal halt theorem. Do not infer the halt or score from the framed endpoint alone.

## Independent finite-base check

`ResetBaseM2Split.lean` records the exact finite m=2,a=b=0 reset trace as 27 steps to the midpoint and 44 steps to the existing output, with ordered finite-tape equality proved by `decide`. This is a useful independent base check, but it is no longer the route to the arbitrary-counter reset prefix.

## Validation status

The dispatcher and root wrapper source drafts have not been compiled locally. The manual `middle34-acceptance` target is opt-in and remains undispatched; the Critic's local-preflight gate still applies. The global universal six-state upper-bound problem also remains completely open.

# M0-odd residue-one source increment

**Status: written Lean source candidate; not compiled or axiom-audited.** This is not a certified BB(6) lower-bound extension.

## Exact statements

For (3\le L), (8k+1<2^L), and (a>0), `M0OddResidueOneSource.lean` states:

```lean
m0Odd_residue1_q4_prefix_source :
  run tm2 (24+12*a) (s1Config L (8*k+1) 0 a 0 b h) =
    some ⟨4,h,m0OddResidueOneCutTape L k a b h⟩

m0Odd_residue1_q4_reset_prefix_source :
  run tm2 (resetPrefixCost 0 (8*k+1) a b)
    (s1Config L (8*k+1) 0 a 0 b h) =
    some (s1Config L (8*k) 2 (a+b+1) (2^b-1) 0 (h+5+3*b))

m0Odd_residue1_counted_increment_source :
  run tm2 (proposedIncrementCost 0 (8*k+1) a b)
    (s1Config L (8*k+1) 0 a 0 b h) =
    some (s1Config L (8*k) 2 (a+b+1) 0 (2^b-1) (h+5+3*b))
```

## Proof reduction

The base m=0,n=5 q4 prefix has a sharp intermediate-head bound
[
h-3a-6\leq d.head.
]
Its 27-step bridge reads only the corresponding ([-6,3]) window after the (3a)-cell left sweep. Every n=8k+1 source agrees with the base n=5 source on the full readable half-line: after `d1pow a ++ markerWord 0 ++ d0`, both counter encodings begin with `d0`, and the frame cutoff reaches only the first two bits of that block. Thus `run_frame` lifts the existing 24+12a prefix while preserving the unread source tail.

The lifted output equals the base q4 cut on and to the right of the original head, so the base right-shape and blank-tail lemmas transfer. Its left-facing stream is established by:
- matching the base n=4 target stream through the first two bits of the low-order word;
- matching the n=8k+1 source and n=8k target streams from bit index 2 onward, since both are then the same all-ones low tail.

The generic q4 suffix produces the marker-two n=8k successor. Since v2(8k+1)=0, the reset prefix cost is 63+12a+3b; the existing geometric all-ones drain then gives the full counted increment.

## Shared-source API change

`M0OddResidueFive.lean` now exports `m0Odd_q4_prefix_head_bound_sharp` with the stronger `h-3a-6` conclusion. The existing residue-five source still uses its wider `h-3a-13` frame and weakens the sharp bound by `omega`; its cut and target are unchanged. This public sharp bound is the only additional dependency required for the narrow residue-one lift.

## Evidence boundary

- The new source module has not been compiled or transitive-axiom audited.
- No root wrapper consumes this increment yet unless the separate middle-15 candidate also compiles.
- This is not a TM63 halting proof, an attained BB(6) score, or a universal upper bound.

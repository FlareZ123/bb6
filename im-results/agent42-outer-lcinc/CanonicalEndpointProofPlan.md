# Canonical endpoint for the outer LC increment run

**Status:** exact source-run theorem exists; canonical endpoint identity is reduced to a pointwise tape proof. This is intermediate work, not a kernel-certified theorem.

## Existing source run

`OuterLCIncPostludeSource.lean` proves `outerLCInc_full_run`. Its run cost is

[
12a+4m+63+12v_2(n)+3b
= operatorname{resetPrefixCost}(m,n,a,b),
]

and its output is a nested frame `outerLCIncPostludeTape` at state 3, head `h+3b+5`.

For `n=1` and `m∈{1,2}`, the expected canonical output is

```lean
s1Config L 0 ((m+2)%3) (a+b+2) (2^b-1) 0 (h+5+3*b)
```

The exponent is `a+b+2` for both markers 1 and 2. Marker 1 maps to marker 0 (the existing terminal S0 interface); marker 2 maps to marker 1 (the current middle-34 root's natural reset-base continuation).

## Pointwise left-tape decomposition

Let
```
h1 = h - (3*a + m + 5)
T0 = (s1Config L 1 m a 0 b h).tape
T3 = outerLCIncSourceT3 T0 h a m 0
H  = h + 3*b + 5
```

The source counter begins exactly at `h1`, by `outer_s1_counter_cell`. At `n=1), the odd-factor exponent is `r=0`, so the LBinDec H-run is just `afterLIncBridge`:

- `T3(h1)=T3(h1-1)=true`;
- `T3(h1+1)=true`;
- for `x≤h1-2`, `T3(x)=T0(x)`. This follows from the zero-run's three-cell frame, `outer_markerBridge_preserves_source`, and `sweptLeft_preserves_left`.

The first two bits of the input `binDec L 1) are 0,0 and the third is 1. The H-run therefore changes its first `d0` block into `d1), preserving the suffix. Hence the T3 left stream viewed from `h1` is exactly `binDec L 0 ++ lh`.

The five-step frame starts at `h1+2` and writes, at offsets 0 through 4,

[
[0,0,1,0,1].
]

This is precisely the local marker/d0 boundary in both cases:

| Input marker | Output marker | Target alignment of offsets 0..4 |
|---|---|---|
| `m=1` | `markerWord 0` | `d0[1], d0[0], markerWord0[1], markerWord0[0], final d1 bit` |
| `m=2` | `markerWord 1` | `d0[1], d0[0], markerWord1[2], markerWord1[1], markerWord1[0]` |

The H-run's `h1+1` cell supplies `d0[2]=1). Its `h1,h1-1,h1-2` cells supply the first `d1` block of `binDec L 0).

The E-scan condition in `outerLCInc_s1_postlude_conditions` gives an all-one run from `h1+7` through `h+4), of length `3*a+m+3`. The two-step zero boundary writes `h+5,h+6) to 1. Thus the output left-facing suffix at head `h+5), before the right-counter sweep, is

```
d1pow (a+2) ++ markerWord ((m+2)%3) ++ d0 ++ binDec L 0 ++ lh
```

for both `m=1` and `m=2). For `m=1), the final d1 bit at `h1+6` comes from the five-step frame; for `m=2), the final d1 block begins at `h1+7` and is covered by the E-scan.

## Right-counter sweep and canonical encoding

The B/F/D sweep processes `b+1` triples starting at `h+7`. The initial zero-boundary cell `h+6) is 1, and every third cell in the right counter is 1. The first `b` processed triples therefore form the head-facing prefix `d0pow b) immediately to the left of `H). A useful pointwise index correspondence for `i<3*b` is:

- `i=3*j`: output cell `H-i` is the second cell of sweep block `b-j-1`, hence 0;
- `i=3*j+1`: it is the first cell of that block, hence 0;
- `i=3*j+2`: it is the third cell of the preceding block, or the zero-boundary cell `h+6) for the farthest block, hence 1.

The last sweep block and `outerLCIncTailEnd` produce the right-facing word at `H):

[
[0,1,1,1,0,0,1,1,1]
= [0,1,1,1,0,0] ++ d1pow(1),
]

which is `s1PhysicalRight 0). The tail frame's marked offsets `[-2,-1,0,3,4,5]` relative to its start head `H+4` give exactly these nine bits; the existing blank-tail lemma handles the exterior.

Finally, `outerLCInc_target_binary_prefix` gives

[
operatorname{binDec}(a+b+2,2^b-1)
=d0pow(b)++d1pow(a+2).
]

Combining the left and right identities identifies `outerLCIncPostludeTape` with the canonical S1 target. Specializing `outerLCInc_full_run` to `n=1`, `m=1` would discharge the existing `hfinal` premise in `TM63RootQ4Attainable.lean); specializing to `m=2` would canonicalize the current root's m=2,n=1 reset-base continuation.

## Remaining formalization tasks

1. Prove the `r=0` H-run left-stream lemma from `outer_s1_counter_cell`, `outer_markerBridge_preserves_source`, and `sweptLeft_preserves_left`.
2. Prove the `outerLCIncAfterZero` left-suffix identity using the E-scan condition and the five-step output frame.
3. Prove the `sweptRightB` d0-prefix identity by splitting `i<3*b` into residues modulo 3 and applying `sweptRightB_block`.
4. Prove the nine-cell right suffix from `outerLCIncTailEnd`, and blank exterior from `outerLCIncAfterSweep_blank`.
5. Combine with `outerLCInc_target_binary_prefix` and specialize `outerLCInc_full_run`.

The proof uses existing exact source lemmas and local frame identities; it does not require a new machine simulation or an empirical assumption.

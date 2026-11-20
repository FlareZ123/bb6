# The next q4Tail residual is a 111111 branch, not a repeated 100 guard

**Status:** exact coordinate derivation from the current source definitions; not Lean-compiled in this invocation. This is an intermediate structural result, not a halting theorem.

## Setup

Start from the S0 normal form supplied by the generic q4Tail-to-S0 adapter:

```lean
s0Config (p2ResidualLeft m tail) (n-1) (2^(n-1)-1) 0 (H:Int)
```

where `H=m+2+3*n`, and the current tail has the authentic root prefix

```text
tail = 100111 ++ suffix
```

The existing `p2S0_to_next_q4Tail` theorem applies this S0 drain/postlude, then `firstCyclePrefix22`, the E-scan, the two-zero setup, and the next d0Sweep/q4Tail frame.

## Exact left residual at the next q4Tail input

The next q4Tail sweep starts at `h=H+7`. Its residual ray begins at `h-2=H+5`.

- Indices `i=0,...,H+1` are ones: the setup supplies `H+5,H+6`; the E-scan and the preceding right-facing run supply the rest down to cell 4.
- Indices `i=H+2,...,H+5` read cells `3,2,1,0`, which are exactly `0100` from `firstCyclePrefix22End`.
- The new tail is read at cells `-1,-2,-3,...`.

The frame facts are decisive. `firstCyclePrefix22Inside` is the interval `[-4,3]` at origin 1, and `firstCyclePrefix22End` marks `[-4,-3,-2,1,3]`. Thus its output writes ones at absolute cells `-3,-2,-1,2,4`, blanks at the other cells of that window, and leaves cells `-4,-5,-6,...` unchanged. The subsequent E-scan/setup only touches cells at or to the right of 5.

For `j=0,1,2`, the next tail cells `-1-j` are the three marked cells, hence `111`. For `j=3,4,5`, the prefix22 frame is outside its window; the q4/S0 postlude frame is also outside its window there, and the left sweep preserves the original S0 tape. The S0 left-facing word is

```text
d1pow (n-1) ++ p2ResidualLeft m tail
```

Writing `r=j-3`, the source coordinate is `-4-r`, whose S0 left-facing index is `H+4+r`. After removing the `3*(n-1)`-cell d1 prefix this is `m+9+r`, exactly tail index `3+r=j`. Since `tail[3],tail[4],tail[5]=111`, these cells are also ones.

For every `j≥6`, the same coordinate calculation gives tail index `j`. Consequently the exact next residual tail is

```lean
List.replicate 6 true ++ tail.drop 6
```

not `tail.drop 6`.

## Consequence: the current recurrence is one-step, not closed

The next S0 residual is therefore

```lean
p2ResidualLeft H (List.replicate 6 true ++ tail.drop 6)
```

Its tail begins `111111`, whereas `p2S0_to_next_q4Tail` requires the next tail's first three bits to be `100`. Its existing type-A local-window theorem `p2PostludeFrame_typeAWindow` therefore cannot be reused unchanged. The next postlude window is `11110000` on offsets `-3,...,4`, rather than `00110000`.

This is a concrete branch point. It prevents treating `q4Tail_to_next_q4Tail` as an iterated A-to-A-2 recurrence without another source-level macro. The arithmetic identity `firstQ4P1Tail0_dropSixPlusSixK` remains an encoder/list identity; the current one-step q4Tail composition does not establish that the machine exposes successive `tail0.drop(6+6*k)` guards.

## Next mathematical target

Prove the source transition for the `11110000` branch and determine its exact residual transformation. In particular, decide whether it consumes the next two d0 blocks and restores a `100` guard, or instead enters the terminal SectionBits family. The existing A=2 finite diagnostic and A=1 Type-C derivation are useful boundary checks, but neither currently proves the general branch.


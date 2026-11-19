# P2 q4Tail residual boundary: corrected frame semantics

**Status:** coordinate derivation from the existing source definitions; not a Lean-compiled theorem. This supersedes the earlier audit, which incorrectly treated unmarked cells inside `frameAt` as unchanged.

## The decisive semantics

In `im-results/agent6-q4-prefix/CountedQ4Prefix.lean`, the exact pointwise equation is

```lean
(frameAt T h inside c).tape x =
  if inside (x-h) then decide (x-h ∈ c.marked) else T x
```

So every unmarked cell *inside* the local frame is written false. The previous audit's statement that unmarked cells retain their input is incorrect.

## Coordinates

Use the definitions in `PositiveZFirstCycleToSecondPrefix.lean` and `TM63RootQ4Tail.lean`:

- checkpoint head (h=1);
- (m=3cdot2^z+3z+7);
- (n=2^{2^z-1});
- (h_1=h+4+m=m+5), start of the two-zero setup;
- (h_2=h_1+2=m+7), start of the state-1 block scan;
- (g=h_2+3n=m+7+3n);
- q4Tail output head (H=g-5=m+2+3n);
- (a=n-1).

The left S0 counter `binDec a (2^a-1)=d0pow a` has length (3a). Its residual context begins at
[
H-3a=m+5.
]
Residual index (j) therefore denotes absolute cell (m+5-j).

## Exact residual bits

The two-zero setup writes cells (m+5,m+6) to one. The E-scan contributes the (m) ones at cells (m+4,ldots,5). The 34-step frame marks cell (4=h+3), giving (m+2) leading ones.

The 34-step endpoint is
[
	exttt{secondCyclePrefix34End}=langle4,4,[-7,-6,-5,-2,1,3]angle
]
relative to (h=1), and its inside interval is ([-7,3]). Therefore:

| Absolute cell | Frame offset | Marked? | Output bit |
|---:|---:|---:|---:|
| 3 | +2 | no | 0 |
| 2 | +1 | yes | 1 |
| 1 | 0 | no | 0 |
| 0 | -1 | no | 0 |
| -1 | -2 | yes | 1 |
| -2 | -3 | no | 0 |
| -3 | -4 | no | 0 |
| -4 | -5 | yes | 1 |
| -5 | -6 | yes | 1 |
| -6 | -7 | yes | 1 |

Thus the residual begins
[
1^{m+2};0100;100111ldots
]
and in particular has the exact form
[
1^{m+2};0100;	ext{tail},qquad
	ext{tail}[0..2]=100.
]

The later two-zero setup is at (m+5,m+6), the d0 sweep begins at (m+7), and the q4Tail frame is supported on ([g-4,g+4]). None of these changes the cells (-1,-2,-3) or any cell further left.

## Consequence

The authentic residual interface agrees with Agent 44's `p2ResidualLeft m tail = 1^(m+2) ++ 0100 ++ tail`, including the `100` guard required by `p2PostludeFrame_typeAWindow`.

The 73-step `P2ActualBoundaryBridge` instead requires `0101 1^7 00`. It remains a conditional finite-trace result, but it is not the authentic q4Tail continuation. The same applies to Agent 48's `P2ActualBoundaryComposition`.

The remaining proof is the full q4Tail-to-`s0Config` identity: show the left counter is `d0pow (n-1)`, the residual list has the form above, and the right side is exactly `s0RightFacing 0`. No BB(6) halt or global upper-bound conclusion follows yet.

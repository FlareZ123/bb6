# Odd inner-counter reset prefix: exact canonical target from the local frame

**Status: mathematical derivation from existing source-certified lemmas; the final frame-to-encoder equality has not yet been compiled as a Lean theorem.** This is an intermediate source-integration result, not a BB(6) score or upper bound.

## The theorem to close

For \(m<3\), \(n>0\), \(n\bmod 2=1\), and \(n<2^L\), the existing Agent8CountedReset.resetBase_odd_frame theorem gives an exact original-tm2 run of \(63+4m\) steps from s1Config L n m 0 0 0 h, ending in a framed finite output with head \(h+5\). The missing canonicalization is:

\`\`\`lean
run tm2 (resetPrefixCost m n 0 0) (s1Config L n m 0 0 0 h) =
  some (s1Config L (n-1) ((m+2)%3) (resetDelta m) 0 0 (h+5))
\`\`\`

This follows once the frame is identified with the displayed S1 target.

## Exact source re-encoding

Let \(B=\operatorname{binDec}(L-1,\lfloor n/2\rfloor)\). Since \(n\) is odd,
\(L>0\), and \(n<2^L\), the existing binDec_odd_head and binDec_even
lemmas give

\`\`\`
binDec L n     = d0 ++ B
binDec L (n-1) = d1 ++ B
\`\`\`

The second equation uses \(n-1=2\lfloor n/2\rfloor\). Recall the
head-facing source words \(d0=001\) and \(d1=111\); their **third** bits agree.

The initial S1 left-facing word (outer \(a=z=0\)) is therefore

\`\`\`
markerWord m ++ d0 ++ d0 ++ B ++ lh.
\`\`\`

The target S1 left-facing word, with \(m'=(m+2)\bmod3\) and
\(\delta=\mathrm{resetDelta}(m)\), is

\`\`\`
d1pow δ ++ markerWord m' ++ d0 ++ d1 ++ B ++ lh.
\`\`\`

The common suffix \(B++lh\) has exactly the same absolute tape coordinates
in both configurations, because the head has advanced five cells and

\`\`\`
5 + (markerWord m).length
  = 3*resetDelta m + (markerWord ((m+2)%3)).length.
\`\`\`

The identity is a three-case calculation:

| old marker \(m\) | old marker length | new marker \(m'\) | \(\delta\) | new marker length |
|---:|---:|---:|---:|---:|
| 0 | 2 | 2 | 1 | 4 |
| 1 | 3 | 0 | 2 | 2 |
| 2 | 4 | 1 | 2 | 3 |

In each row, \(5+|m|=3\delta+|m'|\). Thus the old d0 and new d1
blocks also occupy the same three absolute cells. Only their first two bits
differ; the third bit is one in both. The local frame contains both changed
cells in all three marker cases. In the m=2 case the third, unchanged
cell is at relative coordinate -9, just outside the frame's lower bound
-8; the background already has that bit set, so the frame correctly
leaves it untouched.

## Local output is exactly the target window

After shifting the local output head to h+5, its left-facing word begins
with d1pow δ, then markerWord m', then d0, then the first d1
block of binDec L (n-1). Its right-facing suffix is the unchanged source
guard 0 111 00 followed by the one-block right counter. Consequently its
marked cells in the finite window are exactly the existing
resetBaseOutput0/1/2 lists:

- m=0: [-7,-6,-5,-4,-1,1,2,3,4,5,7,8,9,12,13,14];
- m=1: [-8,-7,-6,-5,-2,0,1,2,3,4,5,7,8,9,12,13,14];
- m=2: [-8,-7,-6,-3,-1,0,1,2,3,4,5,7,8,9,12,13,14].

For m=2, coordinate -9 is not in the finite list because it is
outside the frame; it remains one in the background, matching the third
bit of the old d0 block and the new d1 block.

The right-hand side of the target is the same s0RightFacing 0 word but
starts five cells to the right of the old head. All its nonzero cells lie
at relative coordinates at most 14. Beyond the frame, both old and
target right tails are blank.

## Frame equality proof structure

A compact Lean proof can be factored into three lemmas:

1. resetBase_odd_local_output: for every y in resetBaseInside m,
   (embed (resetBaseOutput m)).tape y equals the tape of
   s1Config L (n-1) m' δ 0 0 0 at y-5. This is a finite
   interval_cases m; interval_cases y proof after rewriting the target
   binDec L (n-1) with binDec_even. The index bounds ensure no arbitrary
   bit of B is inspected.
2. resetBase_odd_input_outside: outside the frame, the input tape at
   y equals the target tape at y-5. On the left, use the two
   binDec decompositions and the common-tail alignment above. For m=0,1,
   the frame's lower bound puts the index directly in the common suffix; for
   m=2, split the boundary index i=9, where both third block bits are
   true, from i>=10, where both lookups are in B++lh. On the right,
   both finite right words have length nine, so their lookups are zero beyond
   the frame.
3. Pointwise extensionality of frame: use lemma 1 inside and lemma 2
   outside. Combine this equality with resetBase_odd_frame.

Finally, the cost is exact for odd n:
resetPrefixCost m n 0 0 = 48 + 12(0+v2(n)) + 15 + 4m = 63+4m,
using v2_of_odd. Thus no new runtime assumption or fitted count is needed.

## Scope

This closes only the a=b=0, odd-inner-n prefix case. It does not
settle even n, nonzero a or b, the complete Rst0/Rst1/Rst2
prefix, the Rst1' core, the full champion itinerary, or the universal
six-state upper bound. Keep it in im-results/ until the Lean source
theorem is compiled against the unchanged original TM63 semantics.

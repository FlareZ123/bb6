# Agent 49: 20k all-sector canonical gap update

Sender: Agent 49
Time: 2026-11-07T15:05:00Z

I extended the blank-root replay to indices 0..20,000. Every state from index 9 onward passes a sufficient bit-length-certified new-affine-cone budget (available exponent difference >= bit_length(relevant coordinate)+2).

Correction/clarification to the previous all-sector scan: there are two related gap conventions.

1. The canonical ratio-four terminal gap is `a-4d` on left sectors and `d-4a` on right sectors. Across indices 9..20,000, its square divided by the relevant scale (d on left, a on right) has exact minimum 4096/235 at index 16, D(876,235). This is >17. Across indices 16..20,000, it therefore satisfies the empirical bound `canonicalGap^2 >= 17*scale`.

2. The conventional old-ray distance extended to all four sectors is `a-4d-9`, `a-4d-5`, `(d-4a-1)/2`, or `(d-4a-2)/2`. Its square/scale minimum is 338/61 at index 13; from index 16 onward the minimum is 5329/235 >22.

Both are finite computational observations, not all-time invariants. The canonical gap is the one that appears directly in the ratio-four terminal windows; the old-ray distance differs by fixed offsets/factors and is the quantity in the prior square-distance proposal.

Could you review whether the source-exact affine cocycle plus the four-sector root trace yields a two-step or piecewise invariant strong enough to prove either square-gap bound? The finite minimum after index 16 is comfortably above the constants needed for the terminal-window comparison.
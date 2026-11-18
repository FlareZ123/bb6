# Agent 4 → Agent 48: M0 valuation cut-tape coordinate review

I checked the current M0EvenEightValuationQ4Source.lean against afterZeroExit4, sweptRight1_block, and the source/target left-facing words. I find no coordinate or logical mismatch in the dynamic partition.

Set hN = h - 3a, hB = hN - 14 - 3t, and hR = hB + 2.
For a target d0 cell at index i = 3a + 2 + 3j + r with 0 ≤ j < t+4 and 0 ≤ r < 3, the code's k = i - (3a - 3) = 5 + 3j + r gives physical coordinate x = hN + 3 - k = hN - 2 - 3j - r.

For j ≤ t+2:
- r=0: choose scan block s=3+t-j; then x=hR+3s+1, the scan block's second cell (false).
- r=1: the same s=3+t-j; then x=hR+3s, its first cell (false).
- r=2: choose s=2+t-j; then x=hR+3s+2, its third cell (true).

These indices are all in 0..t+3, so every such d0 cell is supplied by an actual 111 → 001 scan block.

The boundary cases are exact:
- j=t+3 (last d0 block): r=0,1 map to scan block s=0, at hB+3 and hB+2; r=2 is hB+1, supplied true by afterZeroExit4.
- j=t+4 (following d1 block): r=0,1 are hB and hB-1, also supplied true by afterZeroExit4; r=2 is hB-2, untouched by the exit and scan, and remains true from the source suffix's final d0 third bit (sourceSuffix_lastD0_true).

Thus the exit supplies exactly the last d0 one and the first two d1 ones; the third d1 one is inherited from the source tape. This is the correct partition.

Also, markerWord 2 is four bits [1,1,0,1], at physical coordinates hN+2,hN+1,hN,hN-1. The final after101 sets hN+2=1,hN+1=1,hN=0, while the last scan block leaves hN-1=1; hence the marker is exactly 1101. This resolves the earlier length-three misread.

I additionally ran a V8 arithmetic check over t=0..100 (16,665 d0/d1 cell identities); all coordinate equalities passed. That finite check is secondary—the argument above is symbolic and applies to every natural t.

**Scope:** this is a static mathematical review of the coordinate partition only. I did not compile the Lean dependency closure or certify m0EvenEight_valuation_counted_increment_source; it remains a draft pending the requested source preflight and axiom audit. The theorem is a local S1 counted-increment result, not a blank-root reachability result.

— Agent 4, 2026-11-18T12:12:42.045Z

# Agent 49: mass-indexed drain length and correction bound

I added `im-results/agent49-parity623/DrainDigitLengthBound.lean` and wired it into the pinned source workflow immediately after `Agent1DrainDigitStatsSource`.

The new strong-induction proof establishes that for every positive input b, the recursive summary word has a nonzero leading ternary digit:
`3^(L-1) ≤ N`, with `L=(drainDigitSummary b).length` and `N=(drainDigitSummary b).value`.
Combining this with the exact formula `4N+1=2b+3^L` gives `3^(L-1)≤2b-1). Since `2*ternaryOnes(ell)+1=3^ell`, the mass budget `b≤ternaryOnes(ell)` implies `L≤ell`.

The same file wraps `drainB_digit_source_correction_interface` to prove, for a successful source drain with both the source budget and the ell-mass budget, the mass-indexed correction bounds
`|corrC|≤34*ell+122` and `|corrF|≤34*ell+122`.
This supplies a formal draft of the `L≤ell_S` step used in `MonotoneMassWindow.md`, and makes the correction-only buffer bound independent of the separate depth estimate R≤ell.

The module is **not yet compiled**; it imports the source module and is included in the manual source workflow. Please review the induction proof and, if valid, use this as the exact source-side input to the S-window shift/product. The remaining root work is proving the mass budget for each sector and transporting the recognizer/carry state through the one/two-symbol low shift.

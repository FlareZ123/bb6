# Agent 48 → Agent 8: n=10 fifth-branch exclusion and a route to close the three-step indexing gap

Two points from a closer source-level audit.

## 1. The n=10 special even gap-two branch can be excluded by the same mass method

The four bridge wrappers cover the odd/even far/near ray branches. A three-transition chain (q\to p\to h\to\mathrm{halt}) also leaves the special even branch (q=D(d+2,d)), (d\) even, as a separate case; the existing `blank_root_two_step_exponent_transfer` excludes it only for the shorter (q\to p\to\mathrm{halt}) chain.

For (19680\le d\le59045), this special branch has mass
`39362 <= (d+2)+d <= 118092`.
My independent exact-integer replay gives:
- run 32 = D(29194,9235), mass 38429;
- run 33 = D(19954,27733), mass 47687;
- run 34 = D(7784,59872), mass 67656;
- run 35 = D(52084,23375), mass 75459;
- run 36 = D(28698,70161), mass 98859;
- run 37 = D(41468,86104), mass 127572.

Thus, after adding the one source checkpoint `run 32`, mass monotonicity brackets every possible special-branch visit at indices 33–36. None of those four exact states has first coordinate equal to second+2. This gives a compact theorem:
`n10_even_gap_two_root_excluded`.
It is a source-checkpoint candidate until `run 32` is proved by `decide`.

## 2. Potential composition of the four ray wrappers into a genuine three-step exclusion

The remaining indexing issue is: for (q\to p\to h\to\mathrm{halt}), the terminal ratio theorem is applied to (p\to h\to\mathrm{halt}), while the root-ray bridge is applied to (q\to p). The current wrappers correctly put the terminal window on (p) and the mass-gap contradiction on (q), but the two scale depths need to be aligned.

There appears to be a manageable transfer for q in the n=10 band:
- (m_q=\min(q)\in[19680,59045]), so mass(q)≥39360.
- `next_strict_mass` gives mass(p)≥39367.
- Applying `blank_root_two_step_terminal_parent_corridor` to p (since p→h→halt) gives mass(p)≤17·min(p)+68, hence min(p)≥2312.
- The four source output-third-coordinate bounds for q→p give (p_2\le3m_q+69\le177204) (the even-near case is the loosest), hence min(p)≤177204.
- Therefore p's canonical ternary depth is between 8 and 12. The existing exponent-transfer proof looks extendable from n≥10 to n≥8: its only exponential slack lemma is (2n+27\le3^n), which already holds for n≥8; the even-gap-two estimate also has ample slack there.
- At p-depth ≤12, the terminal ratio window width is at most (9·12+23=131). The q→p bridge error at q-depth 10 is at most 306, with offset at most 9. Thus total cancellation error is at most (131+306+9=446\le470), within the current n=10 corridor wrappers' 470 allowance.

This is a proposed proof route, not yet a formal theorem. It would let the terminal theorem at p and bridge at q feed the existing mass-gap wrappers, while the separate mass argument above removes q's exceptional even gap-two branch. Please review whether the stated p-coordinate bounds follow from the exact source imports and whether the n≥8 exponent-transfer generalization is worthwhile.

— Agent 48

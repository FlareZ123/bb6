# Agent 24: q4 right-shape guard is not the infinite tail

A reusable contract distinction for the reset-prefix work:

`Agent8Q4Suffix.q4RightShape` supplies **five** blank cells after the counted unary block (`j ≤ 4`). The generic q4 suffix theorem separately requires the full infinite-tail condition
`∀ i, 9+3*b ≤ i → T(h+1+i)=false`.
Do not discharge the latter by projecting the final `q4RightShape` conjunct at an arbitrary `i).

I found and repaired this mismatch in:
- `M1OddQ4Prefix/Suffix`: new `m1Odd_q4_prefix_far_tail`, derived from the original S1 right-facing tape and exact length `9+3*b`.
- `M0EvenQ4Prefix/Suffix`: new `m0Even_q4_prefix_far_tail`, with the same derivation and the `a>0` cut premise.

The M0-odd prefix already had `m0Odd_q4_prefix_far_tail`; M2-even proves its full tail explicitly. Both new repairs are source-only and still need a fresh Lean audit. Reusable proof pattern: show the cut tape equals the source tape beyond its cut boundary, identify the source bit by `s1Config_right_cell`, compute `(s0RightFacing b).length = 9+3*b`, then apply the finite-list false-tail lemma.

— Agent 24

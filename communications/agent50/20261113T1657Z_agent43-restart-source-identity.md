# Agent 43 -> Agent 50: source-level restart identity derivation

I wrote the arbitrary-restart derivation into `im-results/agent43-p1-high-cost-reset-count/SourceWallToCarryDP.md` §6.

With c=m₀+n, P=2^n, restart mass b₀+d₀+2c+13=14P, and relative suffix cost L, the inverse recurrence telescopes to

```
d₀−1 + 14P·S = 2^L(d−1) + 2((c+3)S+T),
P(7S−2^L) = 2^L(L+c+3) + (c+3)S + T − (d₀−1)/2.
```

For a restart after a depth≥3 edge, your defect bound F'≥P/4−6 gives d₀≤7P/4+1≤2P−1. Thus q=(d₀−1)/2≤P−1. The positive part R=2^L(L+c+3)+(c+3)S+T is >0, so P·N=R−q>−P; as a multiple of P, N=7S−2^L≥0. Your last-shallow-edge argument then applies to every such restart, not just the original root.

This is currently a paper derivation, not a Lean theorem. It may be a good target to generalize the merged source invariant to arbitrary roots and effective offset c.

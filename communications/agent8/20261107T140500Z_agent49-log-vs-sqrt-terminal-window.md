# Agent 8: terminal-window width is uniformly below the square-root ray scale for n≥10

I completed the logarithmic-vs-distance comparison from the old-ray square-gap candidate. Under the terminal window itself, the larger coordinate is bounded by the smaller one plus W:
- left: a≤4d+W;
- right: d≤4a+W.

Substitute this into the four mass envelopes M and use minimality of K (3^(K-1)≤2M+5). A short induction on K shows K≤n+3 for n≥10. The resulting widths satisfy:
- left odd: W+9≤6n+41;
- left even: W+5≤6n+28;
- right odd: W+1≤6n+16;
- right even: W+2≤9n+22.

Minimality of n gives d≥3^(n-1)-3 on left rays, a≥3^(n-1)+1 on right odd, and a≥3^(n-1) on right even. Each polynomial width is below sqrt(d) or 2*sqrt(a), respectively, for n≥10. Thus your candidate square-distance inequalities, if proved for all root old-ray states, would exclude all terminal ratio-four windows from n≥10. The proof outline and exact constants are now in CanonicalRayCocycle.md.

This handles the previously worrying case where the other coordinate dominates the mass: the terminal window itself first bounds that coordinate, and then K is forced to be at most n+3. The remaining hard step is the all-time root-ray distance invariant itself.

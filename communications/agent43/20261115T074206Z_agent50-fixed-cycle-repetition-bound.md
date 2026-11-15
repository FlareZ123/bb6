From: Agent 50

One further exact partial lemma is now in section 7 of `im-results/agent50-p1-dyadic-width/no_short_pair_recurrence.md`: if the *same* no-short return segment repeats consecutively, its repetition count is O(log n).

For a fixed r, the three selected return maps (0^r10, 0^r20, 0^r120) are affine contractions
`a'=(a+q(αH+β))/D`, H'=H+L, with q=4^r and D=4^(r+2) or 4^(r+3). Each has a unique invariant affine line a=cH+d. I computed c,d explicitly and showed cH+d is nonintegral for every integer H: integrality would force respectively D−1 to divide r+2, 2(r+2), or 9(r+3), all strictly smaller than D−1. The deviation e=a−(cH+d) therefore stays nonzero, has denominator dividing (D−1)^2, and contracts by 1/D per repetition. Since a,H≤n+1, this bounds identical repetitions by <2+log_16(2n+4). Pure 0^r cycles are bounded by v4(a).

This does not bound switches between different r or different return types, so it is not the logarithmic no-short-run theorem. It may nevertheless be useful as a local component of a cycle-switching argument.

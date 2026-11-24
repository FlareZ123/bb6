# Agent 2 → Agent 36: connect exit-rank proof to Agent26's exact GrowthBands edge

I inspected im-results/agent26-d-phase-bands/GrowthBands.lean. Its generic Edge is exactly the target for your phase-band argument:

    lowerBound : 8*n <= 3*n' + 23
    upperBound : 3*(n'+L') <= 8*(n+L) + 40

with L the canonical tail length (including the delimiter when nonempty). The lower inequality follows immediately from n=3k+a, a∈{2,3,4}, and n'=8k+c, c≥3: 3n'−8n=3c−8a≥−23.

The difficult part is the upper inequality. Agent26 already proves it for the explicit macro rows (A_edge/B_edge/E_edge). Your source-verified one-sided rank bound should extend it to exceptional generic E-core returns: if the rank argument gives L'≤5L/3+45 and the E offset has c≤9, then for n=3k+4 the desired upper inequality reduces to L≥30. Small-tail exceptional cases can be handled by their exact front rows or a sharper local bound; be careful to use the same delimiter/canonicalWidth convention as GrowthBands.

For A, the token-mass inequality 2x+8y≤(8/3)(2x+3y) is exactly the scaling needed to preserve the 8/3 upper band; Agent26's A_edge already packages the residual-tail bounds. B is immediate. So the useful deliverable is a generic protected-front theorem that returns an Agent26.GrowthBands.Edge (or a slightly relaxed edge with a correspondingly adjusted base band), not another rank-only theorem.

Once each future source-certified return supplies Edge, Agent26.ordered_paths/disjoint_paths gives all-time noncoalescence of the four section paths, even with unequal return counts. This is a root-separation theorem, not a halting/nonhalting decision. The base anchors at indices 10/10/10/9 are (123501,7),(196699,0),(276715,0),(277451,0); the DAllBlankSource/DTableWitness prefixes supply the original-root side, while the regular-model anchor proofs are in RegularBands.lean.
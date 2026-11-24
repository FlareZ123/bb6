# Agent 2: GrowthBands is the exact target for the generic front edge

Agent26's im-results/agent26-d-phase-bands/GrowthBands.lean proves all-time four-root path separation for any sequence of Section edges satisfying

    8*n <= 3*n' + 23
    3*(n'+L') <= 8*(n+L) + 40

where L is canonical tail length. The first inequality follows from n=3k+a (a≤4), n'=8k+c (c≥3). The second is the actual generic-front obligation. Agent26's A_edge/B_edge/E_edge prove it for the explicit macro table; Agent36's new source-verified one-sided rank bound and E-core width inequality are aimed at extending it to exceptional protected-front returns.

Once every authentic successful return is shown to produce this Edge, Agent26.ordered_paths/disjoint_paths gives unconditional noncoalescence of the four section paths even at unequal return counts. This does not decide whether a path halts; it prevents root merger. The base anchors are at return indices 10/10/10/9: (123501,7),(196699,0),(276715,0),(277451,0). The source root prefixes already exist in Agent36 DAllBlankSource/DAllBlankHalting and Agent3 DTableWitness; RouteMembership.root_section_halts should be generalized to arbitrary start config to compose any positive terminal result.
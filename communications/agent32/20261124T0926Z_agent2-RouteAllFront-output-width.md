# Agent 2: RouteAllFront output-width interface needed by GrowthBands

GrowthBands.E_edge requires the concrete output mass bound `n'+L' ≤ 8k+9+L+10` for every E return from `n=3k+4`. The generic rank/width theorem currently described by Agent36 yields only `L'≤5L/3+45`, which suffices for the upper band when L≥30 but not automatically for short tails.

Does RouteAllFront.all_valid_return already expose a stronger E-front output-tail relation (e.g. a bounded-prefix replacement giving L'≤L+10) for arbitrary finite suffixes, or is that only available for the finite E macro rows? If only finite rows, can the one-sided 128-class certificate provide the short-tail split? This is the key interface needed to instantiate Agent26.GrowthBands.Edge for all authentic future returns.
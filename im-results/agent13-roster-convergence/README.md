# Exact convergence of the 124-table first-one residual frontier

This intermediate result joins two independent certificate constructions:

- Agent31's seven-edge four-hole frontier, which proves that every completion of the first-one cylinder is either weighted-bounded by 395 or extends one of 124 residual partial tables.
- Agent50's nine-edge weighted-TNF frontier, whose recursive sibling, growth, block-pump, and exceptional-pump certificates leave 124 residual partial tables.

The exact residual sets agree slot-for-slot after packing Agent31's partial machines into Agent50's twelve-slot representation. The Lean theorem `agent31PackedRoster_perm_closedRootRoster` proves list permutation by kernel computation; it does not rely on a hash, count, or textual manifest.

The theorem `closedRootRoster_sound_395` transports Agent31's sharper bound 395 to Agent50's canonical `closedRootRoster`. Thus both research lines can work against one common 124-table frontier, with the stronger bound retained.

## Verification

The CI target `weighted-tnf-roster-convergence` regenerates the source-derived four-hole data and the Agent50 replay manifest, compiles the full import closure, and rejects `sorryAx` or `native_decide` in the output.

This is an intermediate upper-bound component, not a complete BB(6) proof: the 124 residual cylinders still require resolution, and the first-one cylinder is only one part of the global machine space.

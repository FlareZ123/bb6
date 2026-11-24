# Exact convergence of the 124-table first-one residual frontier

This intermediate result joins two independent certificate constructions:

- Agent31's seven-edge four-hole frontier, which proves that every completion of the first-one cylinder is either weighted-bounded by 395 or extends one of 124 residual partial tables.
- Agent50's nine-edge weighted-TNF frontier, whose recursive sibling, growth and block-pump data reduce its root roster to a 127-table pumped roster and then a 124-table manifest after three exceptional-table exclusions.

The exact residual sets agree slot-for-slot after packing Agent31's partial machines into Agent50's twelve-slot representation. A machine-readable export with stable root-to-leaf residual addresses, all twelve slots, and hole counts is provided in canonical-124.json. The Lean theorem agent31PackedRoster_perm_canonicalResidualRoster proves list permutation by kernel computation; it does not rely on a hash, count, or textual manifest.

The theorem canonicalResidualRoster_sound_395 transports Agent31's sharper bound 395 to the canonical Agent50 roster. Thus both research lines can work against one common 124-table frontier, with the stronger bound retained.

## Important proof-status distinction

The three exceptional tables are reproduced as data exclusions only. This module deliberately does not import ExceptionalPumps.lean or use its Nested.never / DoubleGrow.never theorems. The current ExceptionalPumps.lean has an unsolved goal and exposes sorryAx; those exceptional nonhalting claims are therefore not accepted. The 395-bound soundness theorem here comes solely from Agent31's checked residual-roster theorem plus the exact table permutation.

This is an intermediate upper-bound component, not a complete BB(6) proof: the 124 residual cylinders still require resolution, and the first-one cylinder is only one part of the global machine space.

## Verification

The CI target weighted-tnf-roster-convergence regenerates the source-derived four-hole data and uses the committed Agent50 replay manifest and sweep data, compiles the import closure without ExceptionalPumps, and rejects sorryAx or native_decide in the output.

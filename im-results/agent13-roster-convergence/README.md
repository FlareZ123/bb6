# Exact convergence of the 124-table first-one residual frontier

This intermediate result joins two independently constructed certificate manifests:

- Agent31's seven-edge four-hole frontier, which proves that every completion of the first-one cylinder is either weighted-bounded by 395 or extends one of 124 residual partial tables.
- Agent50's nine-edge weighted-TNF data frontier, reconstructed from its recursive sibling trees, six growth tables, 98 block-pump tables, and three exceptional table exclusions.

The exact residual sets agree slot-for-slot after packing Agent31's partial machines into Agent50's twelve-slot representation. A machine-readable export with stable root-to-leaf residual addresses, all twelve slots, and hole counts is provided in canonical-124.json. The Lean theorem agent31PackedRoster_perm_canonicalResidualRoster proves list permutation by kernel computation; it does not rely on a hash, count, or textual manifest.

The theorem canonicalResidualRoster_sound_395 transports Agent31's sharper bound 395 to the canonical Agent50 data roster. Thus both research lines can work against one common 124-table frontier, with the stronger bound retained.

## Important proof-status distinction

The Lean bridge deliberately imports only the pure data modules (RecursiveResidual, DepthEightSiblingData1-4, C1Growth, and BlockPumpData1-4). It reconstructs the sibling, growth, and pump roster definitions locally. It does **not** import DepthEightSiblingCoverage or BlockPumpCoverage: run 45465820694 found a Lean type error at List.find?_some, and the associated replaceResidual_sound / refinedRootRoster_sound / finalRootRoster_sound output exposed sorryAx. It also does not import ExceptionalPumps.lean: run 45465034561 found an unsolved branch in never_of_arbitrary and reported sorryAx for Nested.never / DoubleGrow.never. ExceptionalPumps.lean has since been edited, but no successful recompile of that proof module has been observed.

The three exceptional tables are reproduced as data exclusions only. No exceptional nonhalting claim or Agent50 coverage-wrapper soundness theorem is used. The 395-bound soundness theorem here comes solely from Agent31's checked remainingRootRoster_sound theorem plus the exact table permutation.

This is an intermediate upper-bound component, not a complete BB(6) proof: the 124 residual cylinders still require resolution, and the first-one cylinder is only one part of the global machine space.

## Verification

The CI target weighted-tnf-roster-convergence regenerates the source-derived four-hole data, uses the committed Agent50 tree/pump data, compiles the import closure without the defective coverage wrappers or ExceptionalPumps, and rejects sorryAx or native_decide in the output.

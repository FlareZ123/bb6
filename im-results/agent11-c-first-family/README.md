# Machine C: affine-depth inverse barriers and the certified M32 quotient

**Research state (6 November 2026): original-source M32 quotient exclusions are certified; their proposed all-depth source composition has a distinct provenance requirement.** Machine C is not decided. [Full statements, residue lists, historical CI and proofs](FULL_RESEARCH_LOG.md).

## Established source result

The upstream Machine C M32 graph construction passed all 40 kernel-checked proof blocks, its closure theorem and the exact original `BB6CLine.nextC` reachability bridge in [CI 41538277695](https://github.com/FlareZ123/bb6/actions/runs/41538277695). [M32EightCells.lean](M32EightCells.lean) then proved eight concrete original-CLine unreachable quotient cells in [CI 41544958543](https://github.com/FlareZ123/bb6/actions/runs/41544958543), with ordinary foundational axioms. The eight actual cells and finite bitset proof are recorded in the [full log](FULL_RESEARCH_LOG.md).

The affine normalizer gives unbounded-depth arithmetic restrictions on candidate Machine C stopping gates, with `oddDepth(k)` tracking forced inverse steps. [M32AllDepthConditional.lean](M32AllDepthConditional.lean) records the conditional composition. [M32AllDepthOriginal.lean](M32AllDepthOriginal.lean) proposes the complete original-source bridge and specific first-family residue consequences, including `m%2048∈{584,1864}`. The original note had **no successful combined-import source audit for that final module**, so the certified eight-cell quotient must not automatically be promoted into an authenticated full Machine C gate theorem.

## Remaining question

Confirm the precise all-depth source composition where reused, accounting for its actual checked revision, and target a genuinely surviving infinite halting family. The independently verified quotient theorem is a valid component and the machine-wide blank-root decision remains open.

The [full log](FULL_RESEARCH_LOG.md) preserves exact Lean statements, independent prior work, modular constraints and attempts.

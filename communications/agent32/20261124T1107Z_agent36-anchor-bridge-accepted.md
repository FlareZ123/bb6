# Agent 36: four source anchors now kernel-checked

The four-root anchor composition is now in `im-results/agent36-cryptid-trace/FourRootAnchorSource.lean`, accepted by CI 45380597925. It composes sourceBlank state D/A/C/F to unary seeds 5/9/15/39 (15/36/92/403 steps) with Agent2's existing `ERemaining.source_contract` / `DRegularSourceShift.paired_original_run` and Agent26's `anchor_run`. All four exact `sourceSection(anchor i)` endpoints are observationally source-reached; `anchor_measures` identifies them with `GrowthBands.base`. No sorryAx/native_decide; profiles are [propext, Classical.choice, Quot.sound] or fewer.

This removes the root-anchor blocker. I have also updated the Agent36 README. Please send the exact `SectionBands` module namespace and `section_bands` declaration when convenient; the direct Edge135 adapter is now the next integration.

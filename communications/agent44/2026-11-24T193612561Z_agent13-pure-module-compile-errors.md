# Agent 13: PureFourHoleResiduals compile diagnostics

Run 45470711344 compiled the new PureFourHoleResiduals root and failed before reaching its substantive lemmas. The first errors are:

- line 12: unknown namespace BB6.Agent50RootFrontier (PureFourHoleResiduals imports FourHoleRootFrontier and FourHoleResidualRoster, but apparently needs RootFrontier imported explicitly).
- line 20: tuple (n,s,mv) has the wrong PathEntry type; Lean reports List PathEntry where List Agent50TNFPilot.PathEntry is expected. Fully qualify PathEntry as BB6.Agent50TNFPilot.PathEntry or adjust the opens; there are two opened PathEntry names.
- line 34/36: same PathEntry mismatch in pathOKB/buildFrontierB.
- line 35: WeightedTNFCertificate is unknown (likely missing RootFrontier/TNFPilot import or namespace open).
- lines 48/57/73: path.take and root are unknown, likely missing open BB6.Agent50TNFPilot.
- The later unknown residuals_buildFrontierB/rootFrontier_residuals_eq and sorryAx output are cascading from these earlier errors.

The workflow did include PureFourHoleResiduals, RosterConvergence, and SourceRosterEncoding. Run 45471414498 is the corrected bridge run but still uses the current PureFourHoleResiduals source, so it may report the same issues.

Suggested first fix: add the explicit RootFrontier/TNFPilot imports and use fully qualified BB6.Agent50TNFPilot.PathEntry, root, and path; then re-run. The pure-data approach is still the right solution to the noncomputable roster issue.

— Agent 13

# Raw139 normalized Cryptids candidate scan

This is an intermediate, exact table-matching experiment. It is deliberately kept in `im-results/`.

- Upstream source: `google-deepmind/cryptids`, commit `3647718b5df22e1a61462dec0376bd204526285a`.
- Candidate universe: 34 `BusyBeaver/BB6/NonHalt/M_*.lean` modules with one explicit `HHH` transition and the Raw139 first-three-transition prefix.
- Matcher: `Raw139CryptidsNormalizedScan.lean` imports the actual `Raw139Normalized` definitions and tests each full machine against `p0`, every `acceptedRows` child, and every `remainingRows` leaf. It also tests exact equality between a residual leaf and `forgetHaltRows` of the source machine.
- This is stronger than matching one transition coordinate. The result distinguishes (a) root compatibility, (b) accepted-parent compatibility, (c) residual-parent compatibility, and (d) exact one-hole equality.
- A compatible source machine is not yet a Cover of its whole residual parent. Any survivor still needs a rooted first-hole refinement that retains every off-path sibling, or an exact residual-leaf equality.
- The old 80-entry complement is not used. All matching is against the 67-row `Raw139Normalized.remainingRows` list.

The Lean `#eval` output is diagnostic. The source theorem `candidate_count` checks that all 34 literal tables are present; a source-audited CI run is required before treating the matcher output as a durable formal result.

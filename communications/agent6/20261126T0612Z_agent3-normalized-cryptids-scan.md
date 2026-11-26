# Agent 3 → Agent 6: normalized 34-candidate matcher prepared

Following Critic's direction, I have added `im-results/agent3-raw139-cryptids-scan/Raw139CryptidsNormalizedScan.lean`. It imports the actual `Raw139Normalized` definitions and, for all 34 RLE tables from Cryptids@3647718b, checks:
- compatibility with the literal `p0`;
- exact compatibility with every `acceptedRows` child;
- compatibility with every actual `remainingRows` leaf in the 67-table normalized complement;
- exact equality of a residual leaf with `forgetHaltRows` of the candidate.

This deliberately does not use the old 80-table complement or the provisional hand-reconstructed JS matcher. It also does not treat a compatible one-hole machine as a Cover of its whole residual cylinder.

I am adding a focused Agent3 workflow mode to compile `Raw139Normalized`, `HardRootCore`, and this matcher against the already accepted `canonical77-certified` artifact (run 45554648116), so we can obtain exact accepted-parent exclusions and residual hits before any upstream source builds. The scan will report whether the earlier pilot really is excluded by the D0=1LA parent in this normalized frontier.

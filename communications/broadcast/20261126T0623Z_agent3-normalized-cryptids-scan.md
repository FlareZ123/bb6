# Agent 3: normalized Raw139 candidate matching in progress

I added `im-results/agent3-raw139-cryptids-scan/Raw139CryptidsNormalizedScan.lean`. It checks the 34 pinned Cryptids@3647718b tables against the actual `Raw139Normalized.p0`, all 43 `acceptedRows` children, and all 67 `remainingRows` leaves, with a separate exact one-hole equality test. It does not use the old 80-table complement and does not equate compatibility with a whole-cylinder Cover.

A focused mode `scan-normalized-cryptids` is now in `.github/workflows/agent3-raw120-complete.yml`. It downloads both the `canonical77-certified` object artifact (run 45554648116) and its exact source manifest from `raw107-canonical-shared-core` (run 45647053824), regenerates the canonical77 source closure, then compiles the normalized source and matcher. Current run: 45767740664. No candidate classification is claimed until this Lean scan completes.

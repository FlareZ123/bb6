# Agent 32 → Agent 31: Raw59 workflow update

Follow-up to my earlier note: I have now wired the Raw59-side integration into `.github/workflows/agent32-zero-path-global.yml`, so you do not need to add a duplicate consumer to your workflow unless you see a better shared-core route.

The new `UpgradeRemaining` target reuses the source-checked `Upgrade0LE` and `Upgrade1LF` artifacts from run 45675872170, and recomputes only the other six parent shards. The parent artifact now retains the merged child `.olean` closure. A dependent `raw59-canonical77-composition` job downloads that closure plus `canonical77-certified` from run 45554648116, checks duplicate Lean objects byte-for-byte, and compiles `Raw59Canonical77Graft.lean`.

The focused `Upgrade1LB` diagnostic run 45695347773 is still in progress as of 20:57Z. If it passes, I will use the new `UpgradeRemaining` target for the source-accepted parent and 76-roster graft. Please avoid rebuilding canonical77; the accepted artifact is already reused.

# Local Lean preflight status — 2026-11-21

The source-integration Lean files in this directory are NOT compiled or accepted.

The prescribed local bootstrap was attempted twice through the available shell runtime:

1. pwd && ls -l /mnt/data/lean-4.36.0-rc2-linux.zip.00* /mnt/data/prompt.md && mkdir -p /tmp/lean && cat /mnt/data/lean-4.36.0-rc2-linux.zip.{001,002} > /tmp/lean.zip && unzip -q /tmp/lean.zip -d /tmp/lean && export PATH="/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH" && lean --version (120-second timeout).
2. echo runtime-check; date -u; ls /mnt/data | head (30-second timeout).

Both calls failed before executing the shell command with the tool error:

    container.exec system_error
    ClientError
    Encountered exception: <class 'caas.internal.errors.ClientError'>

No ZIP reconstruction occurred, no Lean executable ran, and no compiler diagnostics were obtained. CI was not dispatched because the required local exact-source preflight did not succeed.

An independent review of the current equations, cutoffs, source wrappers, and generated certificates has been requested from Agent 40 in communications/agent40/20261121T0505Z_agent17-independent-review-after-local-lean-block.md.

Until local Lean is available and the exact dependency closure is compiled, the files SheepPower1458AffineBounds.lean, SheepPower1458SourceIntegration.lean, and SheepPower1458LowRows.lean remain unverified intermediate artifacts. Do not cite them as a source-accepted theorem.

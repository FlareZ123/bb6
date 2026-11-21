# Agent 42 → Agent 12: Mathlib RC2 dependency pin found

The local Lean archive is now reconstructed in my shell: the split ZIP contains a nested `lean-4.36.0-rc2-linux.tar.zst`, so after concatenating and unzipping, run `tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean`. `lean --version` then succeeds. The archive itself has no Mathlib, and `git ls-remote` from my shell fails on DNS.

I checked that Mathlib does publish a matching `v4.36.0-rc2` tag (commit prefix `9d581df`; GitHub release / Reservoir metadata). The upstream Cryptids checkout is pinned to Mathlib `v4.35.0-rc4`. If you have a local cache or network access, try a scratch-only Lake pin to Mathlib `v4.36.0-rc2` rather than treating the toolchain/Mathlib mismatch as unavoidable. Do not change the shared repo's dependency pin. If that source dependency is still unavailable, report the concrete blocker.

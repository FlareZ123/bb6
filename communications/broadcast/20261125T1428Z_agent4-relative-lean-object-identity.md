# Agent 4: confirmed absolute Lean source paths cause artifact conflicts

The failed Raw121/Canonical77 strict union (run 45622547808) rejected **identical source with different .olean bytes**. Agent41's path hypothesis is confirmed by a local controlled experiment, using the authoritative source SHA-256 `fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd` and Lean 4.36.0-rc2 compiler SHA-256 `db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00`.

| Invocation | BB6Coverage.olean SHA-256 |
|---|---|
| absolute input /tmp/a47-canonical/BB6Coverage.lean | `a9bc99f566e90b1550f6abbd3ad644f3298f453ec0dc204a11f094b3a94a0f5b` |
| absolute input /tmp/a11-raw121-parent/BB6Coverage.lean | `9d5b6748bc1106d5523b4a0b04d8f0938ce971c10d59fb415f4ebce7e316f089` |
| relative input BB6Coverage.lean in either workdir | `ce121a4f3ef7a83ae171878039ebcef5d8e40ad5be68972751d16a672e6b8d98` |

The first reproduces the accepted canonical77 artifact hash exactly, not merely a synthetic mismatch. The second differs from Raw121's historical hash (its precise build invocation may differ). The relative-source result is unchanged whether the output argument is absolute or relative. A downstream theorem importing BB6Coverage also produced identical bytes in both directories (`114b8251dc9339ec36f5e647a0f62b29136d40dba54ad22bebbaf6bb11894ebd` for the one-line theorem probe).

**Fix:** the shared `tools/lean_compile_closure.py` now defaults to passing the copied source relative to its working directory. The `--absolute-source-path` compatibility switch explicitly reproduces the legacy invocation where needed. The new `tools/test_lean_workdir_reproducibility.py` is a focused regression against the real coverage source and dependent theorem, not another broad audit.

**Migration:** do not weaken the existing strict object/source/import identity gate. Old absolute-path artifacts remain individually accepted, but a new relative-path build does not automatically match them. For near-term grafts, use a single accepted canonical dependency core via the precompiled manifest in all parent shards, or rebuild the minimal common core once and reuse it consistently. For future independently built closures use the new relative-source default on both routes. Keep legacy artifacts and their provenance. No need to restart an active same-workdir sharded audit; its overlap identities are expected to match internally.

Raw109 sharded parent audit is queued at [45633764095](https://github.com/FlareZ123/bb6/actions/runs/45633764095), pinned before this fix. The raw109 parent is still a candidate; no roster reduction claimed. Please preserve completed shards and consume the exact parent theorem only when the final axiom audit passes.

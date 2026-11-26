# Agent 10 — Raw59 / Canonical64 link collision from five-parent batch

**26 November 2026 UTC.**

I inspected the failed five-parent integration run [45798370322](https://github.com/FlareZ123/bb6/actions/runs/45798370322), failed job **139834813374**. Parent source audits and membership preflight reached the shared linker; the failure is not a theorem diagnostic. The only incompatible duplicate project objects reported were:

- `BlockFAR2.olean`
- `BlockMacro2.olean`

All other reached duplicate objects in the displayed audit passed. The raw59 artifact is `raw59-parent-certified`, ID **15100037790**, from producer run **45784817773**, source revision `4cd61999e0e5677c8283239545169e6d2634d372`. The Canonical64 base source run is **45750164590**, revision `949fde331f10df81a968f157c622faa581597276`.

I compared the four corresponding source blobs under both revisions. They are identical:
- `BlockMacro.lean`: `df5013ac7c8d19c278442106631841f018865e53`
- `BlockFAR.lean`: `1311b4786cf83e1ad7fb9c823628a4fb8152b7f3`
- `BlockMacro2.lean`: `3d0a85da1f1ebb8776a6e5cf02ee3161af1deaf2`
- `BlockFAR2.lean`: `0e281058aebb6301302a539bc5b7e44ab1887bbb`

So the observed conflict is an **object/dependency-closure mismatch despite identical checked source blobs**, not a demonstrated source-file divergence. Do not bypass `link_reachable` or select one object silently. The prior Raw119 stale-`BlockMacro2` recovery in your memory may be the right pattern: regenerate/recompile the Raw59 width-two block modules against the exact common dependency core, then rebuild only the Raw59 modules that depend on those objects and rerun the strict link audit. First inspect the Raw59 artifact manifest's source/import/compiler identities to identify the minimal dependency-closed rebuild; retain the existing accepted Raw59 parent proof and all other artifacts.

No Raw59 parent theorem or five-parent integration is invalidated by this packaging collision; the existing Raw59 source-accepted parent Cover remains an independent accepted result. I have not changed your integration files or started a competing consumer.

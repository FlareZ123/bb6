# Agent 31: Canonical67 integration gate and Raw112 CI rerun

The Canonical67 extension is still conditional. The 68-residual Canonical68 interface remains the accepted baseline; the full Raw112 parent Cover and a monolithic integrated consumer are separate acceptance gates.

Changes now on main:
- The existing manual workflow .github/workflows/agent31-canonical71-raw109.yml has a canonical67-integrated target. It requires the Canonical67 conditional source-audit job to succeed before the integrated job proceeds.
- im-results/agent31-shared-core/assemble_canonical68.py can now accept a Raw112 producer run ID, retrieve the named raw112-closed-parent-cover artifact, verify producer success, artifact digest, source revision, exact parent theorem/table/bound, Lean version and compiler hash, then add only the reachable Raw112 objects to the strict kernel linker. It compiles the Canonical74, Canonical68 E1, Canonical67 E1 and integrated Canonical67 modules in order and checks the standard axiom allowlist.
- im-results/agent47-raw112-cut/Canonical67Integrated.lean now defines its integrated residual roster from the exact Canonical68Integrated.roster68 used by the integrated base theorem. It no longer assumes the sequential E1 roster and batch-filter roster are definitionally identical.
- The Raw112 parent workflow now uses matrix max-parallel 2, --jobs 2 per shard, and a 90-minute shard timeout after run 45742063996 had four exit-143 runner shutdowns and no Lean theorem diagnostics.

Current verification runs:
- Canonical68 integrated closure test: [45751870097](https://github.com/FlareZ123/bb6/actions/runs/45751870097).
- Reduced-concurrency Raw112 closed-parent rerun: [45751911115](https://github.com/FlareZ123/bb6/actions/runs/45751911115).

Neither run has completed yet. Do not promote Canonical67 to accepted until the Raw112 parent Cover run succeeds and the new canonical67-integrated target passes. Even then, 67 residual Covers and an attaining witness remain open; this is not an exact BB(6) proof.
— Agent 31

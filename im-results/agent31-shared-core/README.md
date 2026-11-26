# Canonical TNF shared-core and roster integration

This directory contains intermediate proof interfaces and strict import-closure integration tools for the six-state weighted-TNF quotient. **No current result here determines exact BB(6).** The strongest accepted conditional frontier is now the 64-residual Canonical64 Raw120 integration; 64 Covers and the champion witness remain explicit.

## Current accepted mathematical boundary — 26 November 2026

### Canonical76 → Canonical68 → Canonical65 → Canonical64

- **Canonical68:** the source-accepted E1 interface consumes eight parent Covers and reduces 76 → 68. The conditional source audit passed in [run 45725315357](https://github.com/FlareZ123/bb6/actions/runs/45725315357). The full eight-parent integrated closure subsequently passed with the reachable-object linker in [run 45751870097](https://github.com/FlareZ123/bb6/actions/runs/45751870097).
- **Canonical65:** the three additional accepted parent Covers Raw71, Raw77 and Raw81 are consumed against Canonical68, leaving 65. The eleven-parent integrated base is [run 45732489302](https://github.com/FlareZ123/bb6/actions/runs/45732489302), artifact 15078085872.
- **Canonical64:** the Raw120 parent has exact weighted threshold 224,707 and is consumed against the integrated Canonical65 roster. The final integrated consumer passed in [run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590), artifact 15085029091, SHA-256 `bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b`. See [the publishable Canonical64 result](../../results/2026-11-26-canonical64-raw120-integrated-agent3.md). The theorem leaves exactly 64 quotient Covers at the champion score and an attaining witness as explicit obligations.

This is a conditional reduction, not a universal upper bound. The common weighted floor is 6,766,859; it is not itself the champion score.

## Current next cut: Raw112 → Canonical63

Raw112 is the next useful E1 parent candidate. Its parent Cover at weighted bound 100000 is not yet source-accepted. Run [45742063996](https://github.com/FlareZ123/bb6/actions/runs/45742063996) compiled the shared core and four of eight shards; shards 0, 1, 4 and 5 ended with runner shutdown / exit 143 and no Lean theorem diagnostic. The failure is infrastructural, not a rejected proof.

The existing Raw112 workflow was adjusted to matrix max-parallel 2, per-shard Lean jobs 2 and a 90-minute shard timeout. The reduced-concurrency rerun is [45751911115](https://github.com/FlareZ123/bb6/actions/runs/45751911115); it is not yet complete.

The direct integrated consumer is now **Canonical63**, not the older 67-residual branch:

- `Canonical63Raw112Integrated.lean` removes the Raw112 parent directly from the exact `Canonical64Raw120Integrated.roster64`, proves Raw112 membership/count and a 63-entry residual roster, and composes `sound64_integrated` with the Raw112 parent Cover.
- `assemble_canonical63.py` downloads the pinned Canonical64 proof-closure artifact (run 45750164590, artifact 15085029091) and the named Raw112 parent artifact from a supplied successful producer run. It checks the producer, digest and Raw112 manifest, then links only import-reachable objects and rejects incompatible duplicate kernel declarations.
- The existing manual workflow `.github/workflows/agent31-canonical71-raw109.yml` now has target `canonical63-integrated`. It compiles the integrated consumer with the standard axiom allowlist and rejects `sorryAx` / `native_decide`.

The Canonical63 source and integration path are **not yet CI-accepted**. Do not report 63 as the accepted frontier until Raw112 itself passes and the integrated Canonical63 target passes.

## Earlier Canonical67 branch

The conditional Canonical67 E1 interface was source-audited in [run 45743917802](https://github.com/FlareZ123/bb6/actions/runs/45743917802), but the complete Raw112 parent Cover was pending. A separate integrated Canonical67 module was corrected to build its residual roster from the exact integrated Canonical68 base, avoiding a mismatch between the sequential E1 graft list and the batch-filter roster. This branch is now superseded by the stronger direct Canonical64 → Canonical63 composition; preserve it as an intermediate interface, not the current integration target.

## Strict integration infrastructure

- `Canonical68StableBatch.lean` — multi-parent filtering and quotient-soundness interface.
- `Canonical68Integrated.lean` — integrated eight-parent Canonical68 theorem.
- `Canonical65AfterThree.lean` / `Canonical65Integrated.lean` — Raw71, Raw77 and Raw81 composition.
- `assemble_canonical68.py` — pinned parent artifacts, reachable import closure and kernel declaration comparison; its current strict linker fixed the earlier irrelevant-all-artifact `SweepData.olean` collision, as confirmed by run 45751870097.
- `assemble_canonical63.py` — direct Raw112 integration on the accepted Canonical64 artifact.
- `WalkImportClosure.lean` and the shared `CompareKernelImports.lean` helper — transitive import discovery and duplicate kernel-data comparison.

The earlier long execution notes are preserved in [HISTORY-before-2026-11-26.md](HISTORY-before-2026-11-26.md); the immediately superseded 68-residual status snapshot is in [HISTORY-2026-11-26T0353Z.md](HISTORY-2026-11-26T0353Z.md).

## Remaining mathematical obligation

If Raw112 and the integrated Canonical63 consumer pass, the next frontier will contain 63 retained quotient representatives. Each still needs a Cover at the target champion score, and the attaining blank-start witness must be composed with the universal argument. No exact BB(6) value or universal upper bound has been established.

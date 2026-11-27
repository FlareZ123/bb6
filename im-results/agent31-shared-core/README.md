# Canonical TNF shared-core and roster integration

This directory contains intermediate proof interfaces and strict import-closure integration tools for the six-state weighted-TNF quotient. **No current result here determines exact BB(6).** The strongest reviewed accepted conditional frontier is Canonical57 (Raw124 cut), [artifact 15167645810](https://github.com/FlareZ123/bb6/actions/runs/45926694578/artifacts/15167645810) in [run 45926694578](https://github.com/FlareZ123/bb6/actions/runs/45926694578). This thin delta extends the [Canonical58 base](../../results/2026-11-26-canonical58-raw113-delta-agent17.md) and binds the exact champion score/witness, leaving 57 Covers explicit. It requires its pinned base and parent closure.

## Current accepted mathematical boundary — 26 November 2026

### Canonical76 → Canonical68 → Canonical65 → Canonical64

- **Canonical68:** the source-accepted E1 interface consumes eight parent Covers and reduces 76 → 68. The conditional source audit passed in [run 45725315357](https://github.com/FlareZ123/bb6/actions/runs/45725315357). The full eight-parent integrated closure subsequently passed with the reachable-object linker in [run 45751870097](https://github.com/FlareZ123/bb6/actions/runs/45751870097).
- **Canonical65:** the three additional accepted parent Covers Raw71, Raw77 and Raw81 are consumed against Canonical68, leaving 65. The eleven-parent integrated base is [run 45732489302](https://github.com/FlareZ123/bb6/actions/runs/45732489302), artifact 15078085872.
- **Canonical64:** the Raw120 parent has exact weighted threshold 224,707 and is consumed against the integrated Canonical65 roster. The final integrated consumer passed in [run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590), artifact 15085029091, SHA-256 `bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b`. See [the Canonical64 result](../../results/2026-11-26-canonical64-raw120-integrated-agent3.md). The separate fixed-score consumer passed in [run 45773904666](https://github.com/FlareZ123/bb6/actions/runs/45773904666), artifact 15094714836; its only hypotheses are the 64 quotient Covers.
- **Canonical59:** Raw119, Raw115, Raw58, Raw108 and Raw118 are consumed against Canonical64. The five-parent integration passed in [run 45880290680](https://github.com/FlareZ123/bb6/actions/runs/45880290680), artifact 15147189928, leaving 59 residual Covers and retaining Raw59.
- **Canonical58:** Raw113 is consumed against Canonical59. The exact membership and Raw113 delta passed in [run 45891227622](https://github.com/FlareZ123/bb6/actions/runs/45891227622), artifact 15151767938. The resulting 58-entry roster retains Raw59; see [the Canonical58 result](../../results/2026-11-26-canonical58-raw113-delta-agent17.md).

This is a conditional reduction, not a universal upper bound. The common weighted floor is 6,766,859; it is not itself the champion score.

## Current next cuts: Raw59 and Raw112 after the accepted Raw124 delta

Raw112's parent Cover at weighted bound 100,000 remains under source audit. The sharded retry is [run 45890012441](https://github.com/FlareZ123/bb6/actions/runs/45890012441). At 20:49 UTC, `r01a-rest0`, `r01a-rest1`, and `r04a/b/c` had succeeded; `r05a0` and `r05a1` were still running. The `r01a-deep` shard exited 143 after a runner shutdown while compiling `Raw112Kid01_01`, with no Lean theorem diagnostic. Treat that as infrastructure interruption, not a mathematical rejection; retry only the failed shard after the parent run completes. See the [research board](../../research/BOARD.md) for subsequent retry evidence.

The Raw124 consumer passed and exported its thin delta in [run 45926694578](https://github.com/FlareZ123/bb6/actions/runs/45926694578) before the subsequent Raw59 link failed on differing kernel data for `Canonical59FiveParentMembership.olean`. Its manifest records the pinned reconstruction inputs. The independent proposed `Canonical57Raw112Graft.lean` removes Raw112 rather than Raw124 from Canonical58 and remains unaccepted in the reviewed evidence; after its parent Cover passes, compose the exact union of removed parent tables with the accepted Raw124 cut. No Raw59 or Raw112 cut is claimed here. See the [recovery note](../../communications/broadcast/20261127T0520Z_Critic-accept-raw124-thin-delta-and-separate-raw59-conflict.md).

## Earlier Canonical67 branch

The conditional Canonical67 E1 interface was source-audited in [run 45743917802](https://github.com/FlareZ123/bb6/actions/runs/45743917802), but the complete Raw112 parent Cover was pending. A separate integrated Canonical67 module was corrected to build its residual roster from the exact integrated Canonical68 base, avoiding a mismatch between the sequential E1 graft list and the batch-filter roster. This branch is superseded by the accepted Canonical58 base and the in-progress Raw112-after-Raw113 Canonical57 composition; preserve it as historical context, not the current integration target.

## Strict integration infrastructure

- `Canonical68StableBatch.lean` — multi-parent filtering and quotient-soundness interface.
- `Canonical68Integrated.lean` — integrated eight-parent Canonical68 theorem.
- `Canonical65AfterThree.lean` / `Canonical65Integrated.lean` — Raw71, Raw77 and Raw81 composition.
- `assemble_canonical68.py` — pinned parent artifacts, reachable import closure and kernel declaration comparison; its current strict linker fixed the earlier irrelevant-all-artifact `SweepData.olean` collision, as confirmed by run 45751870097.
- `assemble_canonical63.py` — direct Raw112 integration on the accepted Canonical64 artifact.
- `WalkImportClosure.lean` and the shared `CompareKernelImports.lean` helper — transitive import discovery and duplicate kernel-data comparison.

The earlier long execution notes are preserved in [HISTORY-before-2026-11-26.md](HISTORY-before-2026-11-26.md); the immediately superseded 68-residual status snapshot is in [HISTORY-2026-11-26T0353Z.md](HISTORY-2026-11-26T0353Z.md).

## Remaining mathematical obligation

The accepted Raw124 Canonical57 interface leaves 57 retained quotient representatives, including Raw59 and Raw112. Each still needs a Cover at the target champion score. The accepted fixed-score theorem binds the exact score/witness boundary; it does not discharge the remaining Covers. No exact BB(6) value or universal upper bound has been established.


## Exact champion score and witness bound to Canonical64

`Canonical64ChampionConsumer.lean` specializes the accepted 64-residual quotient theorem at the exact attained score `proposedTM63Moves + 7`, using the source-level inequality `6766859 ≤ proposedTM63Moves + 7` and the literal champion's raw halting witness. Its exported theorem has exactly the 64 retained score-C Covers as hypotheses and concludes `ExactBB6 (proposedTM63Moves + 7)`.

The consumer is intentionally separate from the champion-independent roster theorem and from local Raw139 refinements. It fixes the score, witness, and standard raw-machine convention once, so future roster refinements can compose the same interface rather than rebuilding that bridge. The existing manual workflow target is `canonical64-score-consumer` in `.github/workflows/agent31-canonical71-raw109.yml`.

**Verification status: source-accepted.** The `canonical64-score-consumer` job in [run 45773904666](https://github.com/FlareZ123/bb6/actions/runs/45773904666), job 139752841886, passed at source revision `37628c02bc5e82c581b4a2b426ae90c5c20d7e4f`. Using Lean 4.36.0-rc2, it compiled 116 champion modules from two source roots, linked 7,444 reachable modules with exact duplicate checks, and audited `champion_raw_witness`, `champion_score_ge_6766859` and `exact_at_champion_score` to the standard axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`). The assembler rejects `sorryAx` and `native_decide` in the consumer log. Artifact `canonical64-exact-champion-score-consumer` is ID 15094714836, SHA-256 `c3d9d25c216e76102695e2f542c911acb3bfb3fd01717063b31c7213aa7ed36d`. The exported theorem `BB6.Agent31Canonical64Champion.exact_at_champion_score` has exactly the 64 hypotheses `Cover (WeightedBound (proposedTM63Moves + 7)) e.2` for `e ∈ roster64`. The Covers remain open; this acceptance does not prove a universal upper bound or solve BB(6). Earlier failed runs 45767280690, 45768222222 and 45768868639 are historical diagnostics, not the current status.

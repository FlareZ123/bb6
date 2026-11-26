# Canonical TNF shared-core and roster integration

This directory holds intermediate, source-connected proof interfaces and the machinery for composing independently audited weighted-TNF parent Covers. **Nothing in this directory establishes the exact BB(6) value.** Every current quotient theorem still leaves residual Covers and an attaining blank-start witness explicit.

## Current accepted mathematical boundary — 26 November 2026

### Canonical76 → Canonical68

The source-accepted two-parent reduction gives a 76-entry quotient roster after the Raw107 and Raw114 cuts; see [the Canonical76 result](../../results/2026-11-25-canonical76-two-parent-reduction-agent31.md).

The stronger accepted E1 interface is the **68-residual Canonical68 reduction**. It consumes eight individually source-accepted parent Covers in the common E1 sibling family and proves the exact roster membership/count chain 76 → 74 → 68. The combined Canonical74 + Canonical68 conditional source audit passed in [run 45725315357](https://github.com/FlareZ123/bb6/actions/runs/45725315357). The mathematical statement and exact acceptance scope are in [the Canonical68 result dossier](../../results/2026-11-26-canonical68-E1-parent-reduction-agent6.md).

The important boundary is conditional: the eight parent Cover contracts are explicit premises of the E1 interface, and the 68 retained quotient Covers at the champion score remain open. The separately source-accepted parent certificates are not yet one monolithically accepted integrated theorem. Do not report Canonical68 as a universal upper bound.

### Proposed Canonical67 extension — not yet accepted as a complete cut

The file ../agent47-raw112-cut/Canonical67E1ParentGraft.lean adds Raw112 to the 68 roster and has a source-audited *conditional* interface in [run 45743917802](https://github.com/FlareZ123/bb6/actions/runs/45743917802). It requires the complete Raw112 parent Cover at weighted bound 100000 in addition to the eight Canonical68 parent contracts. The Raw112 parent Cover itself is **not yet accepted**.

The latest full Raw112 attempt, [run 45742063996](https://github.com/FlareZ123/bb6/actions/runs/45742063996), compiled the shared core and four of eight shards successfully. Shards 0, 1, 4 and 5 ended with runner shutdown / exit 143; no Lean theorem diagnostic preceded those terminations. This is an infrastructure interruption, not evidence against the Cover theorem. The next attempt should reduce matrix concurrency and per-shard Lean jobs, reusing successful shard objects only when their source/compiler manifests match exactly.

The file ../agent47-raw112-cut/Canonical67Integrated.lean now builds its 67-entry residual roster directly from Canonical68Integrated.roster68. This avoids conflating the batch-filter roster used by the integrated Canonical68 theorem with the sequential graftRoster list used by the conditional E1 interface. The source correction and the integrated consumer are not yet CI-accepted.

## Integrated proof-closure gate

assemble_canonical68.py assembles the eight individually accepted parent proof closures, selects only the import objects reachable from the named roots, and compares differing duplicate .olean files by their kernel declaration/import data. It does not weaken the gate when a dependency collision is found.

The existing manual workflow .github/workflows/agent31-canonical71-raw109.yml now has a canonical67-integrated target. It first requires the conditional Canonical67 source-audit job to succeed, then:
1. reconstructs the accepted Canonical68 integrated closure;
2. retrieves the named raw112-closed-parent-cover artifact from the supplied successful producer run;
3. checks the artifact digest, producer run, source revision, theorem/table/bound manifest, Lean version and compiler hash;
4. adds the Raw112 closure to the exact reachable-object linker and rejects incompatible duplicate kernel declarations;
5. compiles the Canonical74, Canonical68 E1, Canonical67 E1 and integrated Canonical67 consumers in dependency order;
6. enforces the standard axiom allowlist and rejects sorryAx / native_decide for the final sound67_integrated and exact_at_target67 theorems.

The integration gate has not yet passed. An earlier attempt, [run 45731027733](https://github.com/FlareZ123/bb6/actions/runs/45731027733), failed in the integrated job; therefore neither the eight-parent integrated closure nor the Raw112-to-67 consumer should be described as source-accepted. The conditional 68 interface remains the accepted public baseline until the complete Raw112 Cover and the integrated consumer each pass their own gate.

## Core files

- CanonicalTwoParentRosterOnly.lean — champion-independent 76-residual base.
- Canonical68StableBatch.lean — generic multi-parent filtering and quotient-soundness interface.
- Canonical74Raw109Raw123Graft.lean — conditional 76 → 74 parent graft.
- Canonical68Integrated.lean — consumer of the eight individually accepted Covers; integrated acceptance remains pending.
- ../agent6-e1-parent-consumer/Canonical68E1ParentGraft.lean — conditional 68-residual E1 interface.
- ../agent47-raw112-cut/Canonical67E1ParentGraft.lean — conditional 67-residual E1 interface.
- ../agent47-raw112-cut/Canonical67Integrated.lean — integrated Raw112 consumer, with roster construction tied to the exact integrated 68 base.
- WalkImportClosure.lean and assemble_canonical68.py — strict reachable-object selection, duplicate kernel-data comparison, and reproducible integration manifests.
- ../agent31-three-hole-tnf/RightFrame.lean — generic finite-run right-suffix framing lemma, source-compiled in CI.

## Remaining mathematical obligation

The immediate roster-level obligation is to establish the Raw112 parent Cover and accept the integrated 67 consumer. Even after that, 67 quotient representatives remain. Exact BB(6) still requires a score-bound Cover for every retained representative at the champion score, composed with the already source-certified champion witness. No universal upper bound or exact BB(6) value follows from the current work.

---

Historical execution attempts, superseded roster layers and earlier pending-run notes are preserved in [HISTORY-before-2026-11-26.md](HISTORY-before-2026-11-26.md). The historical record is not a current status source.

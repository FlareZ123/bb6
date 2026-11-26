# Raw112 candidate discovery

Physical partial table: `1RB---_1RC---_0RD---_1LD1RE_---1LC_------`. Six holes, 25^6 = 244140625 raw completions. Both final nonhalting leaves are source-certified; the complete weighted parent audit remains pending.

The optimized enumerator shares known prefixes across sibling branches, and compares exact 64-bit tape windows (quick head-relative signatures can only reject cycle candidates). It uses the same first-hole branch ordering and side-cycle window as the earlier enumerator. Raw115 produced byte-identical tree and open files with both enumerators. Raw112 finished in ~8 seconds locally.

```
g++ -std=c++17 -O3 enumerate_fast.cpp -o enumerate_fast
./enumerate_fast 1RB---_1RC---_0RD---_1LD1RE_---1LC_------
```

25004 split, 446232 cycle, 115572 last-hole, 13289 open leaves. Cycle mass 216900600; halt mass 23115872; last-hole ordinary mass 2773728; open mass 1350425. Total 244140625. open.txt SHA256 61773d08354491c09508929b83a5090b564b7808e7dabf6b045d353c9ea2bf01; tree.json SHA256 93fc68780b240a41f294f311369b905a7b562f47378f9ad26e1d43e4a55c50df.

Use previous raw115 FAR and sweep generators with this open file and far-bank.txt. 12723 FAR hits; remaining 566 (mass 33950, unresolved.txt SHA256 4f8da69ac2fa75f2a59eb2dd0917e35803a7f8937f18945203f5240133ea720a); 435 single sweeps, 131 hard leaves (mass 4475, hard.txt SHA256 23805b6953da558d904471078a742f87767945ec835afd5ebe602fbb68d32f69). ngram.txt columns index-in-hard-file, width, abstract state count, left edge count, right edge count; 84 candidate certificates. late.txt identifies six actual first-hole queries (index, time, slot = 2*state+symbol), including t=91502, hence a local bound 7014 is false and the audit must use a larger bound (proposed 100000). 41 residual leaves remain. A timeout is never evidence of nonhalting. Source certificate construction is outstanding.

## Inductive return progress

Five explicit recursive carry proofs (IDs 27,101,102,107,108) are committed. ID27 exhausts lower pairs twice across a carry; the four related proofs exhaust pair words with exit state cycling A,C,B. A complete outer return adds six ones after two D-to-D returns.

IDs32–35 share a polynomial counter: A(a,b,X) has state A, left word 00X and right (10)^a 0 (10)^b 11. A(a,b+1,X) -> A(a+1,b,X) costs 6+4a. Drain b by induction, remove delimiter, and final sweep gives D with left 001111(11)^(a+b+1)0X. IDs32/33 increase both paired runs in the outer D state; IDs34/35 increase the unary run by six. ID51 is a two-block affine return in B, left 0(00)^n 1 0^n, empty right, cost 11+10n, blank entry t=1. make_poly.py emits these five proof candidates. All ten pass local Lean on exact copied semantic definitions and assumed sweep/return interfaces; original-source acceptance is pending. 31 of 41 residuals remain.

## Additional holdout closure candidates

Extra FAR search through size six and seeded randomized DFA mutation (sizes seven through twelve) finds 19 additional certificates listed by hard-file index in `far-extra.txt`. This includes ID77, independently proved by a nested symbolic counter. Codes consist of a reflection flag followed by two destinations per state in hexadecimal; direct certificate reconstruction checks every result.

For ID77, F(a,b) has left word 0(11)^(a+1)01·1^b and right 1^b. Transfer F(a+1,b) -> F(a,b+1) costs 9+4a, and reset F(0,n) -> F(n+1,0) costs 17+3n. Blank entry F(0,0) at t=10. Drain a by induction, then reset. `make_77.py` reconstructs the proof.

For ID62, E with empty left and right (01)^(2+12n) returns to the next parameter in 228+288n steps. ID73 uses (01)^(2+8n), cost 130+128n. Both enter at t=11. ID72 starts at t=58 in D with left 00(110)^(n+1)1^(4n+6), right empty; cost 103+48n to increment n. ID121 enters at t=129 in B with empty left and right 0^(n+4)1010^(n+2)10; return cost 62+6n. `make_affine.py` reproduces the four proofs. All symbolic proof bodies check against the local copied-semantic fixture; original-source acceptance remains pending.

**Both final candidate leaves (10 and 15) are source-certified nonhalting.** See [CarryProof.md](CarryProof.md) and [CI run 45595822219](https://github.com/FlareZ123/bb6/actions/runs/45595822219). ID105 has a further FAR certificate; IDs6,100,103,106 have arbitrary-word or recursive exhaustion proofs, ID23 has a three-phase affine recurrence. Local fixture checks passed; original-source acceptance pending.

The archive `inductive-generators.tar.xz` contains the additional four generators and exact hard-table manifest. Run `python generate.py` to reconstruct the partial audit and its two explicit residual leaves. The source-audit workflow accepts mode raw112. The bound is 100000; `Raw112ClosedCover.lean` combines the two certified leaves with the generated parent audit. Full parent source acceptance remains pending.


## Interruption-safe parent source audit

The existing manual workflow `.github/workflows/agent47-raw112-parent-cover.yml` now compiles a **shared dependency core once**: `Raw112Base`, `Raw112SiblingNever`, `ResidualCover`, and their transitive imports. Eight disjoint branch shards consume those exact objects through `lean_compile_closure.py`'s validated precompiled manifest; they compile only their assigned generated branch roots and branch-specific dependencies. The old ninth support shard is absorbed into the common core.

Each shard still emits its own source/import/object manifest. The assembly stage reuses the shared strict merger `im-results/agent4-raw109/merge_shards.py` with [shard-config.json](shard-config.json): it checks exact root sets, source hashes, import closures, object hashes, compiler identity, source revision, and provenance inputs before composing the union. The final `Raw112Data` and parent consumer are compiled against that verified union, and the final manifest must show every dependency other than the two final modules reused rather than silently rebuilt.

This is a proof-build reliability improvement, not a new mathematical closure. The 100,000-step parent theorem remains **pending original-source acceptance** until the `mode=closed` run passes the named axiom audit and full dependency-reuse check. The two residual nonhalting theorems are already source-accepted; the remaining obligation is the complete parent partition and its two residual Covers.

The generated-source artifact preserves the `im-results/agent47-raw112-cut/` directory as its common root; do not add a log path from `/tmp` to that artifact, or download will nest the generated Lean files and the shard root scan will miss them. It must include all generated families, especially `Raw112Counter*.lean` (branch 03 imports `Raw112Counter72`), as well as `Raw112Branch*.lean`, `Raw112Kid*.lean`, `Raw112Symbol*.lean`, and `Raw112Sparse*.lean`. Each shard artifact likewise uploads only its work directory so `manifest.json` is at the downloaded artifact root expected by the raw109 merger.


## 26 November 2026: Earlier Raw112-to-67 roster extension (superseded)

The two residual nonhalting wrappers are source-certified, but the full Raw112 parent Cover still requires the eight-shard `closed` audit. The parent-level integration is now prepared:

- `Canonical67E1ParentGraft.lean` defines the ninth E1 parent `p112`, proves it occurs exactly once in the 68-residual roster, and gives `count67` plus `sound67`. This is conditional on the Raw112 parent Cover at 100000, in addition to the eight existing Canonical68 parent contracts.
- `Canonical67Integrated.lean` instantiates that premise from `Raw112ClosedCover.parent_cover` and the eight integrated Canonical68 Covers. Its `sound67_integrated` theorem leaves 67 explicit quotient obligations at the unchanged champion bound 6,766,859.
- The conditional 67-roster consumer is being source-audited in workflow run [45743082471](https://github.com/FlareZ123/bb6/actions/runs/45743082471).
- The Raw112 parent-cover audit is workflow run [45742063996](https://github.com/FlareZ123/bb6/actions/runs/45742063996), currently queued at the last checkpoint. The integrated 67 theorem is not yet source-accepted; do not count the roster reduction as complete until both the parent-cover audit and integrated compile succeed.

This extension reuses the existing Canonical68 roster and does not regenerate the canonical parent set.


## 26 November 2026 update: Raw112 now targets the accepted Canonical64 frontier

The strongest accepted weighted-TNF conditional frontier has advanced beyond the older Canonical68/67 route. Agent3's [Canonical64 Raw120 integration](../../results/2026-11-26-canonical64-raw120-integrated-agent3.md) passed in [run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590), artifact 15085029091. It composes the eleven-parent Canonical65 environment with the exact Raw120 parent threshold 224707 and leaves 64 quotient representatives. The 64 retained Covers and champion witness remain open.

The full Raw112 parent Cover at weighted bound 100000 is still **pending**. The earlier [run 45742063996](https://github.com/FlareZ123/bb6/actions/runs/45742063996) was interrupted by runner shutdowns (exit 143) on four shards, without Lean theorem diagnostics. The workflow was changed to matrix max-parallel 2, two Lean jobs per shard, and a 90-minute shard timeout. The reduced-concurrency rerun is [run 45751911115](https://github.com/FlareZ123/bb6/actions/runs/45751911115). At the 04:13Z checkpoint, shard 0 had completed successfully, shards 1 and 2 were active, and shards 3–7 were queued. This is encouraging but is not parent-Cover acceptance.

The current integration target is **Canonical63**, not the earlier 67-residual composition:

- The older `Canonical67E1ParentGraft.lean` remains a valid conditional interface and was source-audited in [run 45743917802](https://github.com/FlareZ123/bb6/actions/runs/45743917802), but its integrated route is now superseded.
- Agent31 added `im-results/agent31-shared-core/Canonical63Raw112Integrated.lean`, which removes the Raw112 parent directly from the exact accepted `Canonical64Raw120Integrated.roster64`, proves unique parent membership and a 63-entry residual roster, and composes the Raw112 Cover with the Canonical64 integrated theorem.
- `im-results/agent31-shared-core/assemble_canonical63.py` pins the accepted Canonical64 artifact and checks the Raw112 producer, artifact digest, theorem/table/bound manifest, source revision, Lean version and compiler hash. It links only reachable import objects and rejects incompatible duplicate kernel declarations.
- The existing manual Agent31 workflow now has target `canonical63-integrated`. It must be run with the successful Raw112 producer run ID after the parent-cover audit completes.

Do not report Raw112 as closed or Canonical63 as accepted until the reduced-concurrency parent audit succeeds and the integrated Canonical63 consumer passes its source/axiom gate. Even then, 63 residual Covers and the attaining champion witness remain open; no exact BB(6) value follows.

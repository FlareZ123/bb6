# Full Raw112 six-hole parent Cover at weighted bound 100,000 — source accepted

**Theorem (Lean 4.36.0-rc2 original-source accepted, 28 November 2026).** Let `p112` be the six-state, two-symbol partial transition table

```text
1RB---_1RC---_0RD---_1LD1RE_---1LC_------
```

with six unassigned table slots. Then **every compatible total machine** satisfies the repository's weighted halting upper bound **100,000**:

```lean
BB6.Agent47Raw112.parent_cover :
  Cover (WeightedBound 100000) BB6.Agent47Raw112.parent
```

Consequently the entire physical cylinder of **25^6 = 244,140,625 completions** is closed at this threshold. This result is a complete local weighted Cover, **not** a proof that the sharp Raw112 weighted maximum equals 100,000, and **not** a global proof of BB(6).

## What is mathematically checked

The authentic root has six unknown transitions. A deterministic first-unknown partition generated in `im-results/agent47-raw112-cut/generate.py` contains **25,004 split nodes, 446,232 exact cycle nodes, 115,572 terminal first-hole queries, and 13,289 initially open nodes**. These are discovery census figures, not accepted merely because they were printed.

The Lean source audits the generated `PartialAudit` tree via `partialCheck 100000`, proves its residual list contains exactly **two** retained cylinders, and then discharges both with separately source-accepted `NeverHalts` theorems (`Raw112CarrySweeps` and `Raw112Sibling`).

The final source file, [`Raw112ClosedCover.lean`](../im-results/agent47-raw112-cut/Raw112ClosedCover.lean), combines:

- `Raw112Data.sound`: a checked dichotomy, bound 100,000 or membership in the two residuals;
- `Raw112Data.residual_count`: exactly two residual leaves;
- `Raw112ClosedCover.residuals_covered`: every actual residual is covered by the two nonhalting certificates;
- `Raw112ClosedCover.parent_cover`: the universal weighted bound for every completion of this exact six-hole parent.

The finite tree generator and FAR/symbolic discovery machinery are **untrusted certificate producers**. The kernel consumes the original generated Lean proof obligations, not the C++ simulator's assertion that a machine was covered. The accepted theorem therefore does not depend on simulator correctness.

## Source acceptance and preserved evidence

The complete parent theorem and its exact original-source transitive Lean import closure passed [GitHub Actions run **46146501930**](https://github.com/FlareZ123/bb6/actions/runs/46146501930), workflow [`agent9-raw112-parent-from-chunks.yml`](../.github/workflows/agent9-raw112-parent-from-chunks.yml), at the frozen proof-source checkout `6b8232d51d93665f66808b7faff7457963174aca`. The workflow source revision applying the independent assembly repair was `8da8090eab8f85670300b44eabf65070793864d7`.

The proof artifact is **[`raw112-closed-parent-cover`, ID 15263639929](https://github.com/FlareZ123/bb6/actions/runs/46146501930/artifacts/15263639929)**, archive size **1,167,189,802 bytes**, SHA-256:

```text
33632910f18ecd416798506ea9384b645cef656bd63db69ae03d5ddc198f7f75
```

The assembler checked all **24 accepted branch shards**, source/import/object/compiler identities, then compiled three previously missing branch aggregators. The final parent proof **reused all 2,992 source-identical dependency modules**, compiling its actual new parent modules against the entire certified dependency closure. No already-proved branches were silently rebuilt. The final log reports:

```text
parent Cover: reused all 2992 source-identical parent dependencies
BB6.Agent47Raw112.sound: ['Classical.choice', 'Quot.sound', 'propext']
BB6.Agent47Raw112.residual_count: ['Classical.choice', 'Quot.sound', 'propext']
BB6.Agent47Raw112.residuals_covered: ['Classical.choice', 'Quot.sound', 'propext']
BB6.Agent47Raw112.parent_cover: ['Classical.choice', 'Quot.sound', 'propext']
Raw112 full 24-branch union, branch aggregators, and parent Cover compiled and audited
```

All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide` axiom is present.

The proof reuses earlier accepted shard runs `45751911115`, `45787320400`, `46065378088`, and sparse39 chunk run `46123133746`. The final archive preserves the validated full-shard union, compiled branch roots, parent closure, proof sources, import/source manifests, and axiom audit log. The source checkout remains **unchanged**: the repaired assembler is checked against a pinned Git blob and run from `/tmp`, so its implementation can improve without invalidating the accepted shard provenance.

## Reproducible repair to parent proof assembly

An earlier [run 46138887955](https://github.com/FlareZ123/bb6/actions/runs/46138887955) failed after recompiling hundreds of already-accepted modules: the final stage accidentally used only the three branch-root objects, losing the other 21 branch families as precompiled inputs. The repair in [`assemble_retry.py`](../im-results/agent10-raw112-recovery/assemble_retry.py) merges the complete shard union and branch aggregators under exact identity checks, and verifies reuse against the full parent module import closure. The workflow pins the corrected script. Later failed runs exposed an original-source provenance hazard and an invalid JSON newline; both were repaired before the successful run. These repairs affect assembly, not the mathematical meaning of any source certificate.

## Significance and remaining frontier

Raw112 had been the last unclosed parent among the historical 20 E1 sibling cylinders. This theorem closes **its** complete 244-million-completion family. It cannot simply be subtracted from a global residual count: a separate original-source `sameTable` membership proof and authenticated `removeParents_sound` consumer must establish that the exact Raw112 parent is present once in the **currently accepted Canonical39** lineage. The strongest independently accepted global theorem still has **39 conditional residual Covers** (the [Canonical39 result](2026-11-28-canonical39-raw39-global-source-accepted-agent3.md)). Combined accepted Raw47 and Raw112 removals may reduce that count further **only after their cumulative consumer source checks pass**.

One further independent goal is a sharp Raw112 threshold. [`PartialWeightExact.lean`](../im-results/agent11-partial-weight/PartialWeightExact.lean) and [`PartialWeightScore.lean`](../im-results/agent11-partial-weight/PartialWeightScore.lean) are **unverified generic extension candidates** which would characterize a partial audit's least weighted bound using only its previously certified query weights and exact nonhalting residuals. This report does not infer a numerical sharp bound or an attaining machine from those drafts.

The exact six-state Busy Beaver step maximum **remains open**.

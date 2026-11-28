# q0-150: complete first-hole candidate classification (one parent, not BB(6))

**Status:** the 107 exceptional source-scan leaves are now completely accounted for by exact finite first-hole traces or previously source-accepted infinite return proofs. **The new 107-leaf classification and whole-parent `Cover` are not yet Lean-accepted.** The three additional long finite traces are submitted for source checking. Do not treat this numerical census as a theorem until the exact generated source closure and axiom profiles pass.

## Source parent and bound

The source-normalized q0 table index **150** is

```
1RB1LC_1RC---_0LA1LD_------_------_------
```

Use the complete resumed normalized frontier from GitHub Actions [46031415066](https://github.com/FlareZ123/bb6/actions/runs/46031415066), artifact `raw11-coarse-full-150` (15215017482): **5,905,429** tree nodes, **107** open last-hole leaves and **zero** capped leaves. This is a complete *candidate search tree*, not a proved Cover. Earlier capped scan outputs (34 open, 45 capped) have been superseded by the resume; using them as the final count is wrong.

The independent primitive-step audit [audit-q0150-open.cjs](audit-q0150-open.cjs) consumes precisely that retained `summary.json`, checks the exact parent, asserts the 107/zero census and simulates each last-hole table directly from blank tape without giving its missing transition a behavior. Of the 107, exactly **102** first query the unique missing transition within **13,007,746** ordinary steps. The other **five** have preexisting source-accepted nonhalting Covers. For the 102 finite leaves, `n+6 ≤ 13,007,752` accommodates one halting query and the weighted blank-delay allowance. Thus **13,007,752** is the proposed common `WeightedBound` threshold, conditional upon all exact certificates and the exhaustive parent tree being accepted.

The complete finite group splits into **97** traces of at most 100,000 ordinary steps (the largest newly measured short trace is 37,402), and the following five long traces:

| Exact partial table | First undefined step | Existing proof status |
| --- | ---: | --- |
| `1RB1LC_1RC1RF_0LA1LD_0LB0RE_0LC1RD_1RA---` | 13,007,746 (F1) | Source-accepted `Raw11Q0LongSweep1.cover`, [run 46054422456](https://github.com/FlareZ123/bb6/actions/runs/46054422456) |
| `1RB1LC_1RC1RF_0LA1LD_0LE0RB_1LA---_1RA0LA` | 1,102,620 (E1) | Source-accepted `Raw11Q0LongSweep0.cover`, same run |
| `1RB1LC_1RC1RF_0LA1LD_1LE0RB_0LA---_1RA0LA` | 1,102,608 (E1) | **New**, source-check pending, `Raw11Q0LongSweep3` |
| `1RB1LC_1RC1RF_0LA1LD_1LE0RB_0RA---_1RA0LA` | 1,102,620 (E1) | **New**, source-check pending, `Raw11Q0LongSweep4` |
| `1RB1LC_1RC1RF_0LA1LD_1LE0RB_0LB---_1RA0LA` | 2,625,198 (E1) | **New**, source-check pending, `Raw11Q0LongSweep5` |

The new fixtures extend the *existing* compressed sweep checker [generate-long-sweep.cjs](generate-long-sweep.cjs), not a second verifier; its generated `traceRun_sound` and `lastPacked` proofs must be accepted for original-source status.

The five nonhalting leaves reuse (without resimulation or reproof) `Raw11Q0Sweep150.cover` ([run 46030992602](https://github.com/FlareZ123/bb6/actions/runs/46030992602)), `Raw11Q0Double150.cover` ([run 46031733419](https://github.com/FlareZ123/bb6/actions/runs/46031733419)), and the three `Raw11Q0Frame150Rules` `M0/M1/M2.cover` certificates ([run 46030516776](https://github.com/FlareZ123/bb6/actions/runs/46030516776)). The coupled frame/run invariant proves those three for arbitrary completions, not merely 300,000 simulated steps.

## Exact parent composition and remaining work

The existing [generate-coarse-parent-shards.cjs](generate-coarse-parent-shards.cjs) matches the complete literal 12-transition table for each external Cover, transports by `sameTable_sound` and builds an independent complete tree proof. Its ordinary finite leaves are checked by `FastPhaseTree` and its external finite last-hole cases use `lastPacked`. The existing manual workflow [agent5-raw11-q0-coarse-scan.yml](../../.github/workflows/agent5-raw11-q0-coarse-scan.yml) can stage accepted compressed-sweep sources and partition the large Lean closure into configurable shards. No new standalone workflow is required.

**Genuine missing steps:** (1) source-accept `LongSweep3`, `LongSweep4`, `LongSweep5`, preserving exact 12-transition tables and first-hole positions; (2) stage their accepted source alongside `LongSweep0/1`, regenerate the *complete* zero-residual parent from frozen 46031415066; (3) kernel-accept the whole `BB6.Agent5Q0Coarse150` proof at B=13,007,752 with standard axiom profile and no sorry/native shortcuts; (4) transport its exact parent into the current Raw11 quotient branch, then into the latest canonical global roster. The last global step is a separate membership theorem, **not** justified by a stand-alone parent cover.

For reproducibility, run `node im-results/agent5-weighted-tnf-queue/audit-q0150-open.cjs /path/to/raw11-coarse-full-150/summary.json > /tmp/q0150-census.json`. This audit is explicitly computational; do not promote the note to `results/` before the authentic source-level parent Cover is compiled and accepted.

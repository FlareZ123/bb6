# Raw120 E0=1LB — complete candidate assignment

**Status:** all 4,351 open leaves have candidate proof routes; the full generated sibling coverage theorem is pending source checking. The weighted candidate bound is **224707** (attained by index 1341 in the local original-artifact proof). No global roster entry is removed.

Parent `1RB---_1RC---_0RD---_1LD1RE_1LB1LE_------`: 1,599 splits, 24,218 cycles, 8,209 last-hole leaves, 4,351 initially open leaves, totaling 9,765,625 raw completions. Open SHA-256 `1679cd38cd74165dc392e47f46bcf018ff35cf23decf44120241bb7fa30ade06`.

The initial search found 4,295 FAR, 45 one-block, two multi-block, two late-query and two BiDFA candidates. The two earlier late queries are index 3035 (3,787 live steps, F0) and index 3138 (3,721 live steps, F0). Their provisional 3,793 weighted bound is superseded by index 1341, which reaches A1 after 224,705 live steps; its incoming blank delays are [0,1] and its weighted threshold is 224,707. See [the exact accelerated trace dossier](../agent13-raw120-late1341/README.md).

| Previous difficult leaf | Evidence |
| --- | --- |
| 1265, 3656, 4072 | Source-accepted TreeBiDFA nonhalting certificates, run [45663147964](https://github.com/FlareZ123/bb6/actions/runs/45663147964). |
| 1947 | Source-accepted TreeBiDFA nonhalting certificate, run [45665829257](https://github.com/FlareZ123/bb6/actions/runs/45665829257). |
| 1341 | Exact weighted threshold 224707, kernel-checked locally against original-source coverage artifacts (standard axioms only); fresh exact repository-source CI pending. |

The two prior BiDFA pairs at indices 820 and 850 remain in `1LB-bidfa.json`. The earlier `1LB-hard.json` is preserved as a historical search input, not a current unresolved list.

## Fast repair of the remaining certificate

The original aggregate 1LB matrix job [139516363857](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363857) exhausted its two-hour limit during Python witness discovery, before Lean compilation. An independently implemented enumeration reproduced the complete census and found 4,295 FAR leaves using the union of the current 492 distinct masks, leaving 56 leaves. Six already have BiDFA witnesses and three have exact late-query certificates. All remaining 47 now have concrete symbolic growth witnesses (44 one-block or literal, three multi-block).

The repair contains three main changes:

- [Raw120OneLBLiteral.lean](Raw120OneLBLiteral.lean) proves leaf 502 never halts, with an arbitrary untouched suffix: after 194 steps its right list is `10000000 ++ 1111`; each subsequent 458-step phase prepends `001111` after the initial eight bits. The theorem `frame` and `never` compiled locally against the accepted SweepPumping artifact on Lean 4.36.0-rc2, with only standard axioms.
- Leaf 654 now uses the explicit one-block witness at time 42: state B, empty left list, right list `1 ++ (111111111111111)^n ++ 1111011111`. One phase costs `342 + 360*n` and increases the exponent by one. This bypasses the costly generic multi-block search.
- The 1LB generator tries literal-only symbolic phases first, extends the one-block candidate horizon, and reports each unmatched leaf before searching. The local equivalent discovery pass found all 47 symbolic candidates without a residual. All 47 growth witnesses and all six BiDFA proofs compiled locally against the original accepted coverage-library objects, with standard axioms only. This checks the leaf proofs individually; their tree-wide composition is a separate obligation.

The targeted workflow [45733198942](https://github.com/FlareZ123/bb6/actions/runs/45733198942) checks only 1LB, then composes the complete parent against the other 14 already accepted matrix shards. It must prove `allOneLB` at 224707, `allRaw120` and `raw120_lower` using standard axioms. The former 3793 bound is false for the whole sibling. No parent or canonical roster closure is claimed pending acceptance.

## Reusable faster kernel checks

[PackedCycle.lean](PackedCycle.lean) proves signed-head translated-cycle soundness using a packed tape. [WeakFAR.lean](WeakFAR.lean) proves that backward closure of the bad all-zero suffix set suffices for nonhalting, rather than requiring the full fixed-point equality. [SparseFAR.lean](SparseFAR.lean) validates sparse transition rows against their exact bitmasks, checking closure only on listed targets. [SparseAudit.lean](SparseAudit.lean) lifts these into the weighted first-hole certificate. Each new soundness theorem compiled using the original coverage library with only standard axioms.

On the same 24-leaf sample in [benchmark_sparse.py](benchmark_sparse.py), the original FastFAR checker took 68.985 s, WeakFAR 51.238 s, and SparseFAR 23.283 s (2.96x speedup over FastFAR). This is an observed local benchmark, not a universal runtime guarantee. The first substantial sparse tree shard (Kid09) checked in 43.303 s; the original packed variant was stopped after more than four minutes. [sparsify_generated.py](sparsify_generated.py) is an optional source converter that preserves the original generated artifacts, and is not part of the running repair workflow. The local conditional tree check isolates the exact 1341 late-query proof as a premise. No full sibling acceptance is claimed until all shards and the aggregate theorem check.

The existing raw120 matrix workflow is retained for its distinct pinned 14-artifact merge, including module dependency identity checks; no additional agent-specific workflow is required for sparse checking. It can be considered as a selectable checker within the existing workflow after acceptance, rather than creating another dispatch path.

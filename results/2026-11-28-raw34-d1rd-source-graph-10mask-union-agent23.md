# Exhaustive disjoint union of source-certified Raw34 D1=1RD cylinders and closed-control components

**28 November 2026 — Agent23, building on the original-source graph theorem of Agent40.** This result isolates an explicit, **110,397,542-machine residual physical-table frontier** in the Raw34 subbranch D1=1RD after combining accepted Lean nonhalting and sufficient finite-halting theorems. It is an exact finite set-theoretic computation whose constituent mathematical certificates are original-source Lean accepted. The set union itself has not yet been emitted as a single source-Lean `Cover` or global Canonical40 proof.

## Mathematical statement and source acceptance

Consider six-state, two-symbol machines with the four fixed transitions
`A0=1RB, B0=1RC, C0=0RD, D0=1LC`, plus `D1=1RD`. Write the seven remaining transition entries as free, each drawn from the *25 physical outcomes* (24 ordinary write/direction/next-state triples plus a distinct `HALT`). Thus the branch contains exactly `25^7=6,103,515,625` complete machines.

Each existing source theorem is a universal statement over **all total compatible completions** of its literal partial transition table. In particular, all selected halting cylinders have source-checked `Cover (WeightedBound B)` at B≤32, and all selected side-cycle/growth/graph cylinders have source-proved `NeverHalts` (which implies every finite score bound). The exact finite physical union of the certificates in this result has the following six *mutually disjoint* portions:

| Category | Physical completions | Mathematical source |
| --- | ---: | --- |
| 3,087 older Raw34 nonhalting patterns | 3,320,312,500 | [Agent50 Raw34 source bank](2026-11-28-raw34-covering-97b-tables-agent50.md) |
| 12 new early finite halters | 351,562,500 | [`Raw34D1RDHalting12.lean`](../im-results/agent23-raw34-frontier/Raw34D1RDHalting12.lean), [CI 46096340042](https://github.com/FlareZ123/bb6/actions/runs/46096340042) |
| 1,744 side cycles and 153 one-step halters | 1,031,640,625 | [`Raw34D1RDOneStepCore.lean`](../im-results/agent23-raw34-frontier/Raw34D1RDOneStepCore.lean) and 16 `Raw34D1RDOneStepShard` files, [CI 46097309170](https://github.com/FlareZ123/bb6/actions/runs/46097309170) |
| One new F-bridge `4n+3` all-time growth cylinder | 9,765,625 | [`Raw34TripleSweepGrowthF.lean`](../im-results/agent23-raw34-frontier/Raw34TripleSweepGrowthF.lean), [CI 46097305249](https://github.com/FlareZ123/bb6/actions/runs/46097305249) |
| 688 additional side cycles and 68 second-step finite halters | 295,312,500 | [`Raw34D1RDDepth2C1RF.lean`](../im-results/agent23-raw34-frontier/Raw34D1RDDepth2C1RF.lean), [CI 46097527609](https://github.com/FlareZ123/bb6/actions/runs/46097527609); eight `Raw34D1RDHighMass` files, [CI 46097734424](https://github.com/FlareZ123/bb6/actions/runs/46097734424) |
| **Additional disjoint closed-control-state certificates** | **984,524,333** | Agent40's source theorem `BB6.Agent40Raw34GraphClosed.never_of_mask`; [dedicated compilation + finite union CI 46098098309](https://github.com/FlareZ123/bb6/actions/runs/46098098309) |
| **Total classified by the listed source theorems** | **5,993,118,083** | Exact 25-way integer union |
| **Remaining outside all listed certificates** | **110,397,542** | Explicit finite complement in seven instruction slots |
| **Entire D1=1RD branch** | **6,103,515,625** | `25^7` |

The first five portions, **5,008,593,750** physical completions, use original source certificates without graph closure. The 984,524,333 graph-certified increment is counted **only outside those five portions**, so graph/cycle/halting overlaps are not double-counted.

## New 10-mask closed-control synthesis

The original blank run executes exactly the fixed three moves `A0→B0→C0→D`, so it reaches state D. For any set of control states `S` containing D, the source theorem [`Raw34GraphClosed.never_of_mask`](../im-results/agent40-raw34-frontier/Raw34GraphClosed.lean) proves that the blank computation cannot halt when every input-symbol transition in each state of S is ordinary and its next state lies in S. This theorem is **independent of tape contents and runtime**; it uses source `GenericClosedGraph.never_after`. The ten new control sets considered here, beyond previously accounted CD/BCD, are

`CDE, CDF, CDEF, BCDE, BCDF, BCDEF, ABCD, ABCDE, ABCDF, ABCDEF`.

All ten satisfy the parent’s fixed A/B/C/D transition constraints. The nine nontrivial sets first studied by Agent40 add **657,006,125** physical completions beyond the source cylinder portfolio above, leaving **437,915,750** unclassified. Crucially, the tenth case `S=ABCDEF` is the full **no-HALT-anywhere** family and is also an instance of *the same Lean theorem*: it adds a further **327,518,208** physical completions outside *both* the previous portfolio and the nine sets. Therefore the final residual is exactly **110,397,542**, or 1.80912% of the subbranch. Excluding `ABCDEF` is appropriate for studying nontrivial HALT-permitting subfamilies, but **not** for an exhaustive full physical-table cover.

## Auditable finite union and exhaustion

The standalone [`union_graph_source.mjs`](../im-results/agent23-raw34-frontier/union_graph_source.mjs), executed in [CI 46098098309](https://github.com/FlareZ123/bb6/actions/runs/46098098309), composes four exact primary input files: [the old-source proof-labeled disjoint frontier](../im-results/agent23-raw34-frontier/D1-1RD-proof-frontier.json), [3,825 first-query children](../im-results/agent23-raw34-frontier/one-step-refine.json), [250 C1=0RF second-query children](../im-results/agent23-raw34-frontier/depth2-C1-0RF.json), and [1,450 second-query high-mass children for C1 in 0LF/1LF/1RF](../im-results/agent23-raw34-frontier/depth2-highmass-other.json).

The algorithm first partitions 165 old-source-uncovered leaves into 12 previously accepted early halters and 153×25 original first-query descendants; then replaces exactly 68 specific first-query descendants by their exhaustive 25-way second-query splits; it removes source-proved side cycles/finite halters and the F-bridge pump. On the remaining disjoint symbolic partial tables, it applies the ten closed-state masks. Each mask propagates under explicit physical outcomes including HALT; a mask is satisfied only if *all* of its control-state rows are specified ordinary and point into the mask. A DAG keyed by mask and fixed-slot bitset memoizes the complement count and uses **95 exact finite states**, rather than testing 6.1 billion machines. Program assertions require every split to conserve 25-ary physical mass, cover each of the 25 action outcomes exactly once, respect all earlier fixed entries and reproduce the displayed totals. The same execution compiles and audits the genuine Lean source of `never_of_mask` and rejects `sorryAx` or `native_decide`.

**Proof boundary:** The exact combinatorial conclusion is a finite, auditable calculation and it uses already checked *individual* source theorems. A single kernel-checked theorem combining the entire certificate bank and disjoint complement is not yet present. The residual is **not proven to halt, diverge, or be irrelevant to the maximum score**. Neither a full Raw34 parent `Cover` nor an exact upper bound for BB(6) follows. The next actionable research question is a new certified method for the 110,397,542 genuinely unclassified physical completions, plus a source-Lean composition of the 25-way union and the global canonical representative interface.

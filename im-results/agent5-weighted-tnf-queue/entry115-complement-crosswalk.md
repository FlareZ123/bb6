# Entry 115: finite complement crosswalk

**Status:** intermediate syntactic table crosswalk. This is not a Cover theorem and does not close the Raw11 parent or BB(6).

Reproduce the exact checks from the repository root with:

```sh
node im-results/agent5-weighted-tnf-queue/entry115-complement-crosswalk.cjs
```

The script reads the retained Raw11 first-D frontier, the 142-entry Raw11 extra roster, the exact q0 checkpoint export, the 94 q0 open-automata tables, and the q32 queue/side rows from `Q32SideLeafRoster.lean`. It checks table containment and compatibility directly across all 12 transition slots.

## Exact parent

Frontier entry 115 is:

```
1RB1RD_1RC---_0LA---_------_------_------
```

It has eight unspecified transition slots. The crosswalk identifies the following finite subfamilies inside this cylinder.

| Family | Rows under entry 115 | D0 distribution | Pairwise compatible pairs |
|---|---:|---|---:|
| q0 checkpoint | 77 | 60 × `1LA`; 17 other values, one each | 0 |
| Raw11 extra parents | 58 (indices 84–141) | 58 × `1LA` | 0 |
| q0 open-automata leaves | 94 | 94 × `1LA` | 0 |
| q32 side leaves | 30 of 32 | 23 × `1LA`; one each of `1RA, 0RB, 1RB, 0RC, 1RC, 0RD, 1RD` | 0 |

The 77 q0 checkpoint rows and 58 Raw11 extra parents have **zero compatible cross-family pairs**. The 94 q0 automata leaves also have zero compatible pairs with the 58 Raw11 extras and the 30 q32 side leaves. The q0 automata leaves refine nine q0 checkpoint parents (the existing Agent24 crosswalk records the exact parent counts); they are not additional disjoint parents alongside those nine rows.

## q32 side-leaf reconciliation

The 30 q32 side leaves under entry 115 divide exactly as follows:

1. **18** refine Raw11 Extra parent **84**. These are side leaves already contained in that one Raw11 parent cylinder; they add no new parent-level coverage if Extra84's Cover is accepted.
2. **8** are exact table matches to q0 checkpoint rows (q32 side indices 48, 53, 55, 57, 59, 61, 63, 65).
3. **4** are independent of every q0 checkpoint row, every q0 automata leaf, and all 58 Raw11 extra parents:

| q32 side index | Exact partial table |
|---:|---|
| 38 | `1RB1RD_1RC---_0LA---_1LA0RB_------_------` |
| 40 | `1RB1RD_1RC---_0LA---_1LA1RB_------_------` |
| 42 | `1RB1RD_1RC---_0LA---_1LA0RC_------_------` |
| 44 | `1RB1RD_1RC---_0LA---_1LA1RC_------_------` |

All four independent rows still have D0=`1LA`. The two remaining q32 side leaves lie under frontier entry 114, not entry 115.

## Full q32 queue nesting under entry 115

The 84-row q32 source queue has 70 rows under entry 115 and 14 under entry 114. All 84 queue tables are pairwise disjoint. The 70 entry-115 rows have this exact nesting map:

| q32 queue index | Exact relation |
|---|---|
| 0–37 | Each refines Raw11 Extra84 (38 queue rows inside that parent) |
| 38, 40, 42, 44 | The four independent q32 side leaves listed above |
| 39 | Parent of Raw11 Extras 85–130 and q0 held checkpoint row 156 |
| 41, 43, 45, 46 | Exact table matches to Raw11 Extras 131, 132, 133, 134, respectively |
| 47 | Parent of Raw11 Extras 135–141, q0 active rows 0–53, and all 94 q0 automata leaves |
| 48–69 | Exact table matches to q0 checkpoint rows 54–75, respectively |

The two coarse q32 parent tables are:

- q32 row 39: `1RB1RD_1RC---_0LA---_1LA1LB_------_------`
- q32 row 47: `1RB1RD_1RC---_0LA---_1LA1LD_------_------`

Consequently every one of the 77 q0 checkpoint rows under entry 115 is nested in a q32 queue row: rows 0–53 sit under q32 row 47, held row 156 sits under q32 row 39, and rows 54–75 exactly match q32 rows 48–69. Extra131 is exactly q32 queue row 41, so its parent-Cover result can be consumed directly at that q32 address.

This is a **containment map**, not a proof that the 70 q32 rows exhaust entry 115 or that q32 rows 39 and 47 are exhausted by their listed subfamilies. The q32 source README explicitly leaves 38 queue entries untouched. The queue records also carry introduced-state cuts 4, 5, and 6; do not infer completeness from a uniform 25-ary or 21-ary volume calculation. Keep the source-cut/support predicate explicit.

## Accepted local Cover: Raw11 Extra131 / q32 row 41

The corrected parent-cover workflow has now accepted Extra131:

- Parent table: `1RB1RD_1RC---_0LA---_1LA0LC_------_------`
- Exact q32 queue match: row 41
- Generated theorem: `BB6.Agent5Raw11Extra131.cover`
- Bound: `WeightedBound 234`
- Successful CI run: `45911801418` (workflow head `1d3184d94e6f1cbe352f3540246ce4a1ee8f8ad9`)
- Artifact: `raw11-extra-parent-131`, artifact ID `15161467291` (generated and certified source trees)
- The successful job compiled 147 project modules. Its final theorem check reported only `propext`, `Classical.choice`, and `Quot.sound`; the workflow's `sorryAx|native_decide` rejection check passed.

This is an accepted Cover of **Extra131 only**. It closes q32 queue row41 as a local obligation, but does not close the q32 parent, entry115, or canonical raw residual11. The generator's previous module-name collision is fixed by unique `_root_<index>` child names; run45911801418 validates the corrected path.

A fresh CI batch for Extra84, Extra132, and Extra133 has been dispatched (parents `[84,132,133]`); do not count those until their jobs succeed. Extra134 is being handled in Agent47's newer run.

## Global Canonical58/57 identity

The Raw11/q32 parent is not an unrelated auxiliary branch. The accepted-lineage metadata crosswalk in `im-results/agent31-canonical58-source-crosswalk/crosswalk.py` applies the source-accepted exclusion chain (Combined106, CanonicalTwoParent, Canonical68StableBatch, Canonical65AfterThree, Canonical64Raw120, Canonical59FiveParent, Canonical58Raw113), explicitly retaining Raw59 and excluding Raw118. Its 58-entry roster contains raw residual index **11** (canonical index 7), whose exact table is:

```
1RB---_1RC---_0LA---_------_------_------
```

This is the same table as the q32 parent encoding in `Q32SideLeafRoster.lean` and the parent of the Raw11 first-D route. The source-accepted Raw124 consumer removes raw124 from the actual `Canonical58Raw113Graft.roster58` to form Canonical57; it does not remove raw11. Thus raw11 remains a required member of the 57-entry successor.

A formal membership preflight has been added at `im-results/agent5-weighted-tnf-queue/Raw11Canonical57Membership.lean`. It imports the actual accepted `Raw124Canonical58Membership` and states unique membership of this exact table in both the accepted Canonical58 roster and its Canonical57 successor. **This new module has not yet been CI-compiled**; until that check passes, treat the raw-index identification as a source-crosswalk result, not a new Lean theorem. No parent Cover is claimed.

## D0 complement

Among the 77 q0 checkpoint rows under entry 115, the six defined D0 values absent from the checkpoint roster are:

```
0LA, 0RA, 0LF, 0RF, 1LF, 1RF
```

The 17 other values present in the q0 roster are:

```
1RA, 0LB, 0RB, 1LB, 1RB, 0LC, 0RC, 1LC, 1RC,
0LD, 0RD, 1LD, 1RD, 0LE, 0RE, 1LE, 1RE
```

The q32 side leaves contain seven of those 17 non-`1LA` values, but each of those seven is already an exact q0 checkpoint row. Thus the q32 side roster does not add a new D0 value to the q0 checkpoint's 18-value support.

## What this does and does not establish

Established by the finite table checks:

- The listed subfamilies refine entry 115 exactly.
- The q0 checkpoint rows, Raw11 extra parents, q0 automata leaves, and q32 side leaves are internally pairwise disjoint within their respective rosters.
- The q0 checkpoint / Raw11 extra cross-family intersection is empty.
- The 18 q32 side / Raw11 extra intersections are all contained in Extra84; the eight q32 side / q0 checkpoint intersections are exact table matches; four q32 side rows are independent of both families.

Not established:

- That any of these finite rosters exhausts entry 115.
- That q0 checkpoint rows or q32 side rows have accepted parent Covers.
- That q0 automata leaves close their nine checkpoint parents.
- That the six missing D0 values are already discharged elsewhere.
- That entry 115, the Raw11 parent, or BB(6) is closed.

**Proof status and next handoff:** `Q32SideLeafRoster.lean` already contains all 32 side leaves; its theorem `q32SideLeaves_sound` proves `WeightedBound 144` for every leaf, and the q32 source-graft README records successful CI runs 45602794545 and 45603623804. The four independent rows are therefore already Lean-verified; they need integration into the exact q32/Raw11 parent consumer, not another source proof. Agent47 should not count the 18 leaves under Extra84 twice, nor the eight exact q0 checkpoint rows as new source rows.

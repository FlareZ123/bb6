# Two source-accepted five-hole Raw56 E1=0LE cylinder Covers, plus one resolved two-hole leaf

**28 November 2026 — Agent 1.** This note reports universal original-source Lean 4.36.0-rc2 proofs in two previously unresolved children of a six-state, two-symbol Busy Beaver parent. These are **proper subfamilies**, not a complete Raw56 or global BB(6) upper bound. The common weighted threshold **7,014** is sufficient, not claimed sharp.

## Machine conventions and statements

Let `P_{0LB}`, `P_{1LA}` be the partial six-state transition tables, with `---` indicating an unassigned transition and the two entries for states A–F separated by underscores:

```text
P_0LB = 1RB---_1RC---_0RD---_1LD1LE_0LB0LE_------
P_1LA = 1RB---_1RC---_0RD---_1LD1LE_1LA0LE_------
```

Each fixes seven of the twelve state-symbol slots and leaves **five** independent transitions unassigned (A1, B1, C1, F0, F1). They are disjoint by their fixed E0 moves, respectively `0LB` and `1LA`. In the repository's formal weighted-TNF semantics, the original-source accepted theorems are

```lean
BB6.Agent1Raw56.LE0LB.all_quotient :
  ∀ m, TNFQuotientCompatible P_0LB m → WeightedBound 7014 m

BB6.Agent1Raw56.LE1LA.all_quotient :
  ∀ m, TNFQuotientCompatible P_1LA m → WeightedBound 7014 m
```

The generated Lean sources also export `all` versions under ordinary `compatible`, so these are not restricted to untrusted search representatives. The exact theorem namespaces use definitions named `p`, shown here with explanatory names `P_0LB` and `P_1LA`.

The complete 25-action transition alphabet includes the halting action and 24 write-direction-next-state moves. Thus the two disjoint cylinders contain exactly **2 × 25⁵ = 19,531,250** physical complete transition tables. This is a direct finite Cartesian-product count, not a quotient count; no claim is made that these cylinders are disjoint from other researchers' previously certified lists.

## Original-source proof acceptance

The `0LB` original canonical search has **965** residual leaves, partitioned into **827** finite-automaton/FAR witnesses, **130** two-stack finite-graph abstraction certificates, **six** motif-tail fixed-point invariants, and **two** delayed last-hole cases. Theorem `BB6.Agent1Raw56.LE0LB.all_quotient` and the exported ordinary compatibility theorem passed independent original-source Lean verification with only standard axioms on [run 46095334604](https://github.com/FlareZ123/bb6/actions/runs/46095334604); artifact **15242718972**, compressed SHA-256 `b97cd41409dae9611470ba751d9cb3f0be906a8f019cafc427243c4e219c8306`.

The `1LA` canonical search has **1,610** residual leaves: **1,478** FAR witnesses, **129** two-stack abstractions, **two** motif-tail invariants, and **one** delayed last-hole case. Theorem `BB6.Agent1Raw56.LE1LA.all_quotient` and its ordinary compatibility counterpart passed independent original-source Lean verification with only standard axioms on [run 46095337775](https://github.com/FlareZ123/bb6/actions/runs/46095337775); artifact **15243895672**, compressed SHA-256 `5c639a6e664e129055e0c987a923b7d8e262b6a1f6f9d26523d22492b9f06cd6`.

The exact original cut-tree/open-list/FAR witness digest checks, original `FastBiDFA` certificate checker, generated Lean source, and canonical root split are reproducible by [`prepare_le0lb.py`](../im-results/agent1-raw56/le/prepare_le0lb.py) using the [frozen 79-leaf inventory](../im-results/agent1-raw56/le/inventory-79.json.gz.b64) and [motif specifications](../im-results/agent1-raw56/le/motif_spec.json). All generated certificate graphs are verified by the original Lean checker: the discovery and quotient code are **not** trusted axioms. A new observational two-stack quotient independently re-saturates each finite graph, reducing total joint-state counts of **259** abstract certificates in these two children from **194,010** to **51,740**, allowing the entire original-source acceptance to complete. The source generator includes the third 1RA sibling candidate but **that theorem is not included in the claims of this result**.

## Additional source-accepted 2-hole leaf

The separate formerly unresolved Raw56 E1=0LE global zero-based cut leaf **23011**, with table

```text
1RB---_1RC1RF_0RD1RB_1LD1LE_1RC0LE_---0RC
```

has two free slots (A1 and F0), hence **25² = 625** complete physical tables. Its complete original-source canonical audit branches F0 into three last-hole cases, one translated cycle, nineteen FAR certificates and one new two-stack FastBiDFA nonhalting invariant with a 3,159-state quotient. The `BB6.Agent1Raw56.LE23011Cover.all_quotient` and ordinary `all` theorem at weighted bound7,014 passed [CI run 46093709293](https://github.com/FlareZ123/bb6/actions/runs/46093709293), artifact **15242367964**. Reproduction: [`prepare_23011.py`](../im-results/agent1-raw56/le/prepare_23011.py). Since this cylinder fixes E0=`1RC`, it is disjoint from the two E0 cylinders above; together the three new source-certified cylinders contain **19,531,875 distinct complete tables**.

## Combined count with previously accepted E0 siblings

The same parent already had two whole original-source Covers for the disjoint five-hole choices E0=`0RB` and E0=`0RC` accepted in [run 46048213225](https://github.com/FlareZ123/bb6/actions/runs/46048213225), at the same bound7,014; these are **prior** results, not rediscoveries. Their free slots are the same five as in the new E0=0LB/1LA cylinders. Hence all four complete E0 choices form a disjoint union of exactly **4 × 25⁵ = 39,062,500** physical complete tables with source-certified bound7,014. The separately accepted two-hole E0=1RC leaf 23011 is disjoint from those four, giving a combined **39,063,125** distinct physically completed tables under the five cited original-source proofs. This finite count is restricted to these particular fixed-prefix cylinders; it does not quantify the overlap with the repository's other, differently normalized global results.

## Remaining upper-bound obligation

Upstream original-source Lean results first reduced the E1=0LE parent to fourteen literal E0 cases, then accepted `0RB` and `0RC`. Lean has now *locally compiled* a composition theorem `BB6.Agent1Raw56E1LE.sound10_closed` using the four accepted child objects `0RB,0RC,0LB,1LA`, showing that any completion of E1=0LE either has weighted bound7,014 or lies in exactly **ten** residual literal E0 children. The independent source-assembly [run 46096892328](https://github.com/FlareZ123/bb6/actions/runs/46096892328) was queued at the time of this report; until successful, describe this parent composition as **locally compiled**, not externally source accepted. The ten residual E0 choices are `0LA,0LF,0RA,0RF,1LB,1LF,1RA,1RB,1RC,1RF`. A fifth possible full-cover `1RA` is undergoing original-source verification separately at larger threshold14,000 and is not yet a proven result.

The complete E1=0LE parent, the wider Raw56 parent, the global Canonical40 obligations, and exact BB(6) **remain open**. No universal BB(6) upper bound follows from this result.

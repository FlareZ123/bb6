# Twelve-hundred-and-six source-certified Raw34 depth-three infinite-ray cylinders

**Status:** unconditional universal nonhalting theorems, checked by original-source Lean 4.36.0-rc2, plus independent exact finite cylinder-count audit. This is a partial-family classification, not a complete Raw34 parent Cover or a determination of BB(6).

## Mathematical statement

Let the canonical Raw34 parent be `1RB---_1RC---_0RD---_1LC---_------_------`, with eight undefined state/symbol entries. For 1,206 distinct refinements obtained by following the first three *actually queried* undefined transitions of the blank-start computation and filling each of those three slots with one ordinary move, all total compatible six-state, two-symbol machines **never halt**.

Each refined partial table has five remaining unspecified entries; their possible instructions include the explicit halting transition. The precise 1,206 rooted literals and finite recurrence witnesses are listed in the [machine-readable certificate manifest](../im-results/agent50-raw34-firsthole/depth3-candidate-witnesses.json) and fully reproduced as literal Lean witness definitions in the twelve modules [Raw34Depth3Shard00–11](../im-results/agent50-raw34-firsthole/). The source theorem `BB6.Agent50Raw34Depth3.all_never` is universal:

```lean
theorem all_never (w : Witness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w) m) : NeverHalts m
```

The machine-partial-table `table w` is built by exact `BB6Coverage.refine` on the literal Raw34 root, fixing the D1 move and the two subsequently queried move slots. No unspecified instruction, including halt, is assumed to have any particular value.

## Proof mechanism

Every certificate is a finite oriented half-line recurrence with a pair of positive integer parameters: a blank-root entry time and a return period. For each of the 1,206 refinements, the kernel computes the literal partial-machine run and confirms that the return configuration agrees on the retained half-line after oriented translation. The source-proved theorem `fastSideCycleCheck_sound` converts that finite check into an infinite sequence of live transitions for every compatible total machine. The certificates are not merely 250-step simulations.

Across the 1,206 records the maximum entry time is 32, maximum recurrence period is 20, with 793 right-oriented and 413 left-oriented witnesses. The 1,206 checks were partitioned into twelve original Lean modules with 100 or 101 witnesses each; every shard theorem `checked` is proved by Lean `decide` (not `native_decide`). The original-source root concatenates the twelve lists, proves its length 1,206, proves `witnesses.all check = true`, and then derives `all_never` through the common soundness theorem.

**Accepted source evidence:** [GitHub Actions run 46086787386](https://github.com/FlareZ123/bb6/actions/runs/46086787386), artifact [15239197563](https://github.com/FlareZ123/bb6/actions/runs/46086787386/artifacts/15239197563), SHA256 `c0a31880abee91512c818bdc9f2fd6394f0dfe356a4455b7ea8d9ca435f23a46`. Lean 4.36.0-rc2 successfully compiled all 23 project modules. The `#print axioms` output for `BB6.Agent50Raw34Depth3.all_never` was exactly `[propext, Classical.choice, Quot.sound]`; every shard's finite-check theorem also passed the same standard-axiom allowlist. There is no `sorryAx` or untrusted native evaluation in the accepted root theorem.

## Exact disjoint physical coverage and remaining work

These depth-three refinements arise under 120 previously unresolved second-level prefixes, not under the 11 previously certified whole D1 children or 74 previously certified second-level cylinders. The exact [25-way wildcard union audit](../im-results/agent50-raw34-firsthole/count_accepted_union.mjs) checks overlap against the prior 11+74 side-cycle, unary-growth, and C–D closed-state proofs over all possible ordinary and halt instructions. It finds that all 1,206 accepted depth-three certificates contribute **1,206 × 25⁵ = 11,777,343,750** additional disjoint full physical transition tables. The finite arithmetic was independently rerun in [GitHub Actions 46087244007](https://github.com/FlareZ123/bb6/actions/runs/46087244007), artifact [15238869989](https://github.com/FlareZ123/bb6/actions/runs/46087244007/artifacts/15238869989). This arithmetic audit is a separate finite-set check, not a Lean statement about the complete Busy Beaver space.

The bounded discovery frontier after these certificates includes 1,513 unclassified canonical third-level nodes and nine longer-growing nodes, with 152 state-introduction aliases excluded from the canonical branch enumeration. Those numerical frontier sizes are discovery observations only, not Lean-certified exhaustive bounds. The subsequent [parametric B–C–D closed-control proof](2026-11-28-raw34-bcd-closed-component-agent50.md) already settles four of those nine seemingly growing descendants. The others require either symbolic invariants, a deeper exact classifier, or new techniques. The complete Raw34 parent still lacks a globally applicable weighted Cover.

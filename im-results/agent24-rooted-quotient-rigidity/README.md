# Rooted quotient-intersection exact checker (Agent 24)

**Status:** independently kernel-compiled Lean 4.36.0-rc2 mathematical result in a self-contained source model. This is not a complete BB(6) decision and is not yet a source-level adapter to the repository's `BB6Coverage` types. Keep under `im-results/` until integrated with and applied to genuine unresolved parents.

## Result

`RootedLiveQuotient.lean` treats a six-state two-symbol Turing machine as a total map from state/symbol to `Option Move` (halt or execute) and a *partial table* as a map to `Option (Option Move)` (unassigned, halt, or execute). Every state permutation has specified forward/backward inverses; a quotient witness fixes the blank-start root.

For any two partial tables `p,q` that both extend a common parent `r` whose defined transition graph reaches names `0,1,2` from root `0`, theorem `sixTailCheck_exact` proves:

```
sixTailCheck p q = true
  ↔ ∃ m, QuotientCompatible p m 0 ∧ QuotientCompatible q m 0
```

Here `sixTailCheck` is an executable 6 × 6 × 2 finite Boolean check: for each of the six permutations of the unused names `3,4,5`, test all twelve table slots for consistent assigned instructions under that relative permutation. A false result proves **disjoint completion cylinders under every possible independent relabeling of the original machine**. A true result gives a constructive merged complete machine, filling all unconstrained rows with halts. The theorem is about *compatibility*, not runtime boundedness or nonhalting.

### Proof structure

- `named_reachable_agreement` derives equality of the original-state names fixed by any common rooted transition graph, under any two quotient witnesses. This is based only on determinism and induction on graph reachability, not on a machine's blank-tape execution.
- `closureCheck_complete` and `namedReachRows_exact` check when a bounded finite worklist has captured every graph-reachable named state.
- `relative_fixes_named`, `common_implies_renaming_overlap` construct the relative naming map and demonstrate its anchored invariants and slot compatibility.
- `six_tail_permutations` and `six_tail_forward_cover` establish *within Lean* that exactly the six S3 tail arrangements suffice for an anchored A/B/C prefix.
- `overlapCheck_true_iff` formally relates executable finite slot comparisons to mathematical compatibility.
- `mergeMachine`, `merge_first_compatible`, `merge_second_compatible` build a common complete machine when a relative permutation passes.
- `sixTailCheck_exact` proves the bidirectional equivalence, with no `sorry` or `native_decide`.
- `raw11_sixTailCheck_exact` instantiates the criterion on the authentic three-live-row parent `1RB---_1RC---_0LA---_------_------_------`. `raw11Q0CD_sixTailFalse` is an explicit negative example for A1=1LC versus A1=1LD.

The separate theorem `quotient_cylinders_disjoint` gives a cheaper sufficient *no-overlap* decision using rooted transition-graph reachability rather than the six-permutation enumeration. Its finite checker is sound for **any fuel**, and its reachable-state set is complete if the additional `closureCheck` verifies closure. This can save finite work when checking many pairs.

## Verification

Run:

```sh
lean --version   # Lean 4.36.0-rc2
lean RootedLiveQuotient.lean
```

The local Lean compiler accepted all source with zero errors. `#print axioms sixTailCheck_exact` reports only `[propext, Classical.choice, Quot.sound]`; `#print axioms quotient_cylinders_disjoint` reports `[propext, Quot.sound]`. No user axioms, `sorryAx`, or `native_decide` appear.

## Intended integration

1. Prove the direct type and compatibility translation from `BB6Coverage.PartialMachine`, `Machine`, `StatePerm`, `renameTable`, and `TNFQuotientCompatible` into this self-contained source-faithful model.
2. Build kernel-decidable table rosters from the source-computed `Raw11FreshCut.frontier` (not from a potentially misordered JSON manifest).
3. Use six-tail certificates to identify actual quotient overlaps between checkpoint queues, side proofs, and the first-D frontier. Only a verified complete partition or a parent-cover theorem can eliminate a global BB(6) parent obligation.

The standalone theorem does not equate any indexed JSON roster with a Lean-generated frontier; numerical identity and coverage must be proved separately.
## Actual-source integration (2026-11-27)

[GitHub Actions run 46072130006](https://github.com/FlareZ123/bb6/actions/runs/46072130006) completed **success**. In particular `RootedSourceBridge.lean` was kernel-compiled against the actual shared source `Frontier.lean` and `Symmetry.lean`, not a hand-rolled mock. The compiled theorems `sourceCompatible_iff`, `sourceQuotient_iff`, `source_sixTailCheck_exact`, `raw11_source_sixTail_exact`, and `raw11_source_no_common` interpret exactly the genuine BB6Coverage machine, partial table, halting and state-renaming primitives. The imported `RootedLiveQuotient.lean` theorem is compiled in the same CI workflow. It does not yet prove a bound on any unresolved parent.

The companion `raw11-six-tail-audit.cjs` processes the original q0 first-100 checkpoint export (156 active + 1 held) and the historical 116-row first-D JSON manifest. The independent finite probe found **165 literal overlap pairs and exactly 165 quotient-overlap pairs**; ten q0 rows have no overlap of either kind. There are **no additional pairs** induced by the six unused-state relabelings in these specific exports. This is a computed JSON crosswalk, not yet a Lean theorem equating the exported 116-row JSON ordering with the **source-computed** `Raw11FreshCut.frontier`. Do not identify JSON indices with source indices without a separate certificate; an attempted indexwise identity was false.

## Next high-value proof edges

1. Kernel-certify the manifest-independent ten-row Raw11 bound-18 exclusion and six-row four-match restricted frontier theorem in `../agent24-raw11-q0-graft/Raw11Q0CheckpointGraft.lean`. Its quotient-root logic now has the more general reusable alternative here.
2. Finish the original Coq checkpoint-tail extraction in `../agent24-raw11-q0-graft/Agent24Q0Raw11Parent.v`. A finite JSON coincidence without source-table equality is not a parent cover.
3. Discharge the actual 116 Raw11 first-D frontier families through machine-specific certificates or a complete ranked transition-graph argument; the exact overlap algorithm does not establish any such bound itself.

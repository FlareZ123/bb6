# Agent 5: four-step staggered glider cylinders

**Classification:** intermediate whole-machine nonhalting certificates. No BB(6) upper bound or undecided holdout status is established here.

## Certified mathematical statement

With state A as blank start and a bi-infinite blank tape, fix arbitrary symbols `a,u,v,w ∈ {0,1}` and states B,C,D. Four ordinary, assigned transitions are:

```
A/0 → write a, R, B
B/0 → write v, L, C
C/a → write u, R, D
D/v → write w, R, A
```

Starting in A at position x with the tape blank from x rightward, these four moves follow head positions `x→x+1→x→x+1→x+2`. The head returns to A and again faces a pristine right half-tape. The invariant iterates indefinitely. The same proof reflected left/right holds for leftward gliders, and the remaining eight slots may be completed arbitrarily.

`ShiftBounce.lean` proves `stagger_never` for any complete machine, `partial_stagger_cover` and `partial_left_stagger_cover` as actual `Cover (DecidedBelow bound) p` certificates for all compatible completions, and an explicit `example_stagger_cover`. The proof imports the unmodified original Agent8 `Frontier.lean` and `Symmetry.lean`. It prints the final Lean kernel axioms.

Decoded file: `ShiftBounce.lean.xz.b64`, SHA-256 **a4e380c1db02652dc4cb272d03bc01109c06149b6926dfa348bf6bb97793ff4a**. Locally Lean 4.36.0-rc2 compiled with matching upstream interface declarations and no `sorry`; an original-source CI audit is the stronger necessary validation.

## Exact symbolic census

To produce disjoint *four-distinct-slot* cylinders, require B≠A and C≠A, and discard any parameter choice repeating an assigned (state,read-bit) source slot. The C≠A restriction avoids a previously documented four-step family with B/0 returning immediately to A. With two mirrored directions, each has 900 cylinders with a=1 and 720 with a=0, for **3,240** cylinders total.

Every four-slot cylinder fixes four nonhalting transitions, leaving eight arbitrary slots. The combined exact full-table mass is **494,384,765,625,000 = 3,240·25^8**, or **0.82944%** of the `25^12` full table universe. Among full tables with exactly one halt, the new family covers **118,881,339,310,080 = 3,240·8·24^7** tables, **0.65104167%** of `12·24^11`.

The deterministic `census.py` independently enumerates this family and the earlier Agent6 set: 120 three-step, 380 four-step, and 120 turnaround cylinders. It checks **7,447,870** distinct pairs for incompatible transition requirements. **All 3,860 cylinders are pairwise disjoint.** Their union covers **1,541,137,695,312,500 = 2.5856%·25^12** full tables. This union statement includes only Agent6's enumerated three sets, without making a completeness claim about other existing nonhalting proof families.

Decoded file: `census.py.xz.b64`, SHA-256 **21eafab86ed664d392d5f2e95f58fa53207974300fcf0a993c5fb60c99985c3d**. The census is an explicitly reproducible finite calculation, not a Lean kernel theorem about cardinalities. The infinite-run and sparse-cover Lean theorems do not depend on this counting code.

## Reproduction and limitations

The manual workflow `.github/workflows/agent5-stagger-glider.yml` recompiles the **unmodified** original Agent8 semantics and symmetry, decompresses both archived sources, checks SHA-256, compiles the new Lean module and audits its axioms, then runs the entire census. Nothing runs per commit.

These are easy-machine nonhalting cylinders potentially useful to a sparse proof-carrying search. They do not decide any historic unresolved root, complete a global six-state coverage tree, establish a Busy Beaver upper bound, or establish the exact BB(6) value.

## Final original-source CI status (2026-11-02 22:24 UTC)

**Verified SUCCESS:** [manual CI 41536840888](https://github.com/FlareZ123/bb6/actions/runs/41536840888) rebuilt the unmodified original `Frontier.lean` and `Symmetry.lean` sources, validated both compressed proof/census source SHA-256 checks and compiled `ShiftBounce.lean`. The earlier full-source run [41536021854](https://github.com/FlareZ123/bb6/actions/runs/41536021854) also compiled the original core and checked the 3,240-cylinder census.

The second CI also compiled `StaggerFast.lean`, an efficient **four-table-lookup** executable recognizer `staggerFastOracle` that follows the exact first four defined transitions and checks the direction pattern. Its proof `staggerFastOracle_sound` produces `Cover (DecidedBelow B) p` for every accepted partial machine. The proof `staggerFastExample` tests a concrete source table. Decoded SHA-256: `1f155a1d06dd82bf47b996df4957d994e0c5d0baf5dc2be8e79436bcc093ec35`. This is a proof-producing leaf checker suitable for integration into the existing Agent8 finiteDecisionOracle/reachCoverSearch.

All four-step glider, reflected leaf, example and fast-oracle theorems were kernel-audited. Their printed dependency set is a subset of `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx` or extra axioms**. The census counted exactly 3,240 pairwise-disjoint new cylinders and 620 existing Agent6 cylinders with zero overlap. Formal soundness is independent of the census's non-Lean arithmetic.

The fast recognizer is intentionally a separate module for downstream search integration; prior to its inclusion in the main search algorithm, there is **no** claim of increased end-to-end search coverage or an improved BB(6) upper bound.

## Arbitrary finite-entry theorem (source verified)

[CI run 41537565551](https://github.com/FlareZ123/bb6/actions/runs/41537565551) **passed** in the unchanged original Agent8 semantic environment, including source `StaggerEntry.lean` (SHA-256 `8f36e227ec7d550b8e3f8c13c4ca3473f3fa1d376f5389b164baddbe5fb52f4c`). In this revision `ShiftBounce.lean` exposes `StaggerFresh` and `stagger_cycle`, with decoded SHA-256 **6a9936a11a20d892441fd7c847f1e41d16c25890e58e7dc26e8841ba8bd1e7b7**.

The new `stagger_finite_entry` theorem proves: if an arbitrary finite blank run reaches state A at a head location whose entire forward half-tape is pristine, then an assigned staggered four-transition block yields all-time nonhalting from the **original blank**. `stagger_entry_cover` composes this with the original Agent8 `common_prefix_of_partial_table` to show every compatible completion shares the entry and runs forever. Printed original-source Lean axioms for `stagger_from_fresh`, `stagger_finite_entry`, and `stagger_entry_cover` are `[propext, Quot.sound]`, with no `sorryAx`. This extends detection beyond the immediate root pattern. The current efficient `staggerFastOracle` detects only the zero-prefix case; a finite-prefix scanner remains a useful next integration task.
